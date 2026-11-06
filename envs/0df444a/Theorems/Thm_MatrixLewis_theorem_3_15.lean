-- Prove2me | Theorems.Thm_MatrixLewis_theorem_3_15
-- name    : MatrixLewis.theorem_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:15:12.657202+00:00
-- url     : https://prove2.me/theorems/a1b50012-8719-4503-842b-5cedae2b2167
-- title:
--   Theorem 3.15 — gradient of $f_q$ and barrier parameter $m$
-- statement:
--   Throughout, $A_1,\dots,A_m, C$ are real symmetric $n\times n$ matrices, the $A_i$ satisfy Assumption 3.1 (linearly independent, with $\bigcap_i \ker A_i=\{0\}$), and $q>2$ is real; $p=q/(q-2)$ and $p'=q/2$.
--
--   For every $S\succ0$ and $\dot S\in\mathbb S^n$, with $X=S^{-1/2}\dot SS^{-1/2}$,
--   $$
--   D\varphi_q(S)[\dot S]=-\operatorname{tr}(\Lambda_SX).
--   $$
--   Consequently, for $x\in\mathcal D$ and $h\in\mathbb R^m$, $Df_q(x)[h]=-\operatorname{tr}\bigl(\Lambda_{S_x}X_{S_x}(h)\bigr)$. Moreover, for every $S\succ0$, $S'\succeq0$ and $x\in\mathcal D$,
--   $$
--   D\varphi_q(S)[S'-S]\le m,\qquad \|\nabla f_q(x)\|_{M_x,*}\le\sqrt m ,
--   $$
--   where $\|u\|_{N,*}=(u^\top N^{-1}u)^{1/2}$.
--
--   Differences from the source:
--   - encoding: Dφ_q(S)[Ṡ]; ∇f_q(x) → derivative of t ↦ φ_q(S + tṠ) at 0; the vector (Df_q(x)[e_i])_i of Fréchet derivatives; reason: φ_q is real analytic; the gradient's coordinates are the partial derivatives
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Theorem 3.15, pp.24–25, eqs. (29)–(32)

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_barrier
import Definitions.Def_MatrixLewis_localNormSq
import Definitions.Def_MatrixLewis_lineDeriv

namespace MatrixLewis

/-- **Theorem 3.15** (Gradient and barrier parameter `m`; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), pp.24–25, eqs. (29)–(32)).
For every `S ≻ 0` and every `Ṡ ∈ Sⁿ`, with `X = S^{−1/2}ṠS^{−1/2}`, `Dφ_q(S)[Ṡ] = −tr(Λ_S X)`.
Consequently, for `x ∈ 𝒟` and `h ∈ ℝᵐ`, `Df_q(x)[h] = −tr(Λ_{S_x} X_{S_x}(h))`. Moreover, for every
`S ≻ 0`, `S′ ⪰ 0` and `x ∈ 𝒟`, `Dφ_q(S)[S′ − S] ≤ m` and `‖∇f_q(x)‖_{M_x,∗} ≤ √m`.

**Formalization Note** `Dφ_q(S)[Ṡ]` is the derivative along the line `S + tṠ` (`lineDeriv 1`);
`Df_q(x)[h]` is the Fréchet derivative `fderiv`; `∇f_q(x)` is the coordinate vector
`(Df_q(x)[eᵢ])ᵢ` and `‖u‖_{N,∗} = (uᵀN⁻¹u)^{1/2}` (p.14). Standing assumptions of §3 (symmetric
`Aᵢ`, `C`; Assumption 3.1; real `q > 2`) are hypotheses. -/
theorem theorem_3_15 {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (h31 : Assumption31 A) (hq : 2 < q) :
    -- (29)
    (∀ S Sdot : Matrix (Fin n) (Fin n) ℝ, S.PosDef → Sdot.IsHermitian →
      lineDeriv 1 (potential q A) S Sdot =
        -(lewisWeight q A S * (mpow (-(1 / 2 : ℝ)) S * Sdot * mpow (-(1 / 2 : ℝ)) S)).trace) ∧
    -- (30)
    (∀ x ∈ dom A C, ∀ h : EuclideanSpace ℝ (Fin m),
      fderiv ℝ (barrier q A C) x h =
        -(lewisWeight q A (slack A C x) * scaledDir A (slack A C x) h).trace) ∧
    -- (31)
    (∀ S S' : Matrix (Fin n) (Fin n) ℝ, S.PosDef → S'.PosSemidef →
      lineDeriv 1 (potential q A) S (S' - S) ≤ m) ∧
    -- (32)
    (∀ x ∈ dom A C,
      let g : Fin m → ℝ := fun i => fderiv ℝ (barrier q A C) x (EuclideanSpace.single i 1)
      Real.sqrt (dotProduct g ((lewisMetric q A C x)⁻¹.mulVec g)) ≤ Real.sqrt m) := by sorry

end MatrixLewis
