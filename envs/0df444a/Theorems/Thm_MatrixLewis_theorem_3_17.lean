-- Prove2me | Theorems.Thm_MatrixLewis_theorem_3_17
-- name    : MatrixLewis.theorem_3_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:14:52.812199+00:00
-- url     : https://prove2.me/theorems/1b4b4506-b2aa-4641-b8f2-4062c07c568b
-- title:
--   Theorem 3.17 — Hessian sandwich $M_x\preceq\nabla^2f_q(x)\preceq(q+1)M_x$
-- statement:
--   Throughout, $A_1,\dots,A_m, C$ are real symmetric $n\times n$ matrices, the $A_i$ satisfy Assumption 3.1 (linearly independent, with $\bigcap_i \ker A_i=\{0\}$), and $q>2$ is real; $p=q/(q-2)$ and $p'=q/2$.
--
--   Let $S\succ0$ and $\dot S\in\mathbb S^n$. Then
--   $$
--   Q_S(\dot S)\le D^2\varphi_q(S)[\dot S,\dot S]\le(q+1)\,Q_S(\dot S).
--   $$
--   For every $x\in\mathcal D$,
--   $$
--   M_x\preceq\nabla^2f_q(x)\preceq(q+1)M_x .
--   $$
--   In particular $\varphi_q$ is strictly convex on $\mathbb S^n_{++}$ and $f_q$ is strictly convex on $\mathcal D$.
--
--   The Lewis metric approximates the Hessian within the factor $q+1$.
--
--   Differences from the source:
--   - encoding: D²φ_q(S)[Ṡ,Ṡ]; ∇²f_q(x); P ⪯ Q → second derivative of t ↦ φ_q(S + tṠ) at 0; the matrix (D²f_q(x)[e_i, e_j])_{ij}; (Q − P) positive semidefinite; reason: φ_q is real analytic; standard Lean forms
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Theorem 3.17, pp.27–28, eqs. (39)–(40)

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_barrier
import Definitions.Def_MatrixLewis_localNormSq
import Definitions.Def_MatrixLewis_lineDeriv

namespace MatrixLewis

/-- **Theorem 3.17** (Hessian sandwich; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), pp.27–28, eqs. (39)–(40)). Let `S ≻ 0` and
`Ṡ ∈ Sⁿ`. Then `Q_S(Ṡ) ≤ D²φ_q(S)[Ṡ, Ṡ] ≤ (q + 1)Q_S(Ṡ)`. For every `x ∈ 𝒟`,
`M_x ⪯ ∇²f_q(x) ⪯ (q + 1)M_x`. In particular, `φ_q` is strictly convex on `Sⁿ₊₊`, and `f_q` is
strictly convex on `𝒟`.

**Formalization Note** `D²φ_q(S)[Ṡ, Ṡ]` is the second derivative along `S + tṠ`; `∇²f_q(x)` is the
matrix `(D²f_q(x)[eᵢ, eⱼ])ᵢⱼ` of the second Fréchet derivative; `P ⪯ Q` is
`(Q − P).PosSemidef`. Standing assumptions of §3 are hypotheses. -/
theorem theorem_3_17 {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (h31 : Assumption31 A) (hq : 2 < q) :
    -- (39)
    (∀ S Sdot : Matrix (Fin n) (Fin n) ℝ, S.PosDef → Sdot.IsHermitian →
      localNormSq q A S Sdot ≤ lineDeriv 2 (potential q A) S Sdot ∧
        lineDeriv 2 (potential q A) S Sdot ≤ (q + 1) * localNormSq q A S Sdot) ∧
    -- (40)
    (∀ x ∈ dom A C,
      let H : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j =>
        iteratedFDeriv ℝ 2 (barrier q A C) x
          ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ)]
      (H - lewisMetric q A C x).PosSemidef ∧ ((q + 1) • lewisMetric q A C x - H).PosSemidef) ∧
    StrictConvexOn ℝ {S : Matrix (Fin n) (Fin n) ℝ | S.PosDef} (potential q A) ∧
    StrictConvexOn ℝ (dom A C) (barrier q A C) := by sorry

end MatrixLewis
