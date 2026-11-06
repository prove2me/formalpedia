-- Prove2me | Theorems.Thm_MatrixLeeSidford_theorem_2_1
-- name    : MatrixLeeSidford.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:37:56.766195+00:00
-- url     : https://prove2.me/theorems/9202546f-1b7d-462d-8925-e115e3e9fcfb
-- title:
--   Theorem 2.1 — the matrix Lee–Sidford barrier $10^6s^2\Phi_p$ is a $10^6s^2m$-self-concordant barrier for $\Omega$
-- statement:
--   Let $A_1,\dots,A_m,C\in\mathbb S^n$ with $m\ge1$, and assume that $\Omega=\{y\in\mathbb R^m:S(y)\succ0\}$ is nonempty, the $A_i$ are linearly independent, and $\bigcap_i\ker A_i=\{0\}$. Let
--   $$
--   s=2\lceil\log(2mn)\rceil,\qquad \alpha=10^6s^2,\qquad \nu=\alpha m,\qquad F=\alpha\Phi_p .
--   $$
--   Then for every $y\in\Omega$ and $h\in\mathbb R^m$, with $B_i$, $B_h$, $L_y$, $K_y$ at $y$:
--   1. **(a)** The minimum in (2.1) is attained at a unique matrix $G_*=G_*(y)\succ0$, the optimal weight, which depends smoothly on $y$, and
--   $$
--   \operatorname{tr}\big[L_y(G_*)^s\big]=m,\qquad \Phi_p(y)=-\frac12\log\det G_*+\frac m{2s}-\frac m2 .
--   $$
--   2. **(b)** $F$ is a $\nu$-self-concordant barrier for $\Omega$: its Hessian is positive definite, $F$ diverges at every boundary point of $\Omega$, and
--   $$
--   |\nabla^3F(y)[h,h,h]|\le2\big(\nabla^2F(y)[h,h]\big)^{3/2},\qquad |\nabla F(y)[h]|^2\le\nu\,\nabla^2F(y)[h,h].
--   $$
--   3. **(c)** With $W_y=L_y(G_*)^{s-1}$, the gradient matrix $M_y=\frac12\big(L_y(G_*)^s+\sum_{i,j}(G_*)_{ij}B_iW_yB_j\big)$ and the proxy Hessian $Q_y[h,h]=\operatorname{tr}[M_yB_h^2]$ satisfy $M_y\succ0$, $\operatorname{tr}[M_y]=m$,
--   $$
--   (\nabla F(y))_i=-\alpha\operatorname{tr}[M_yB_i]\ (i\in[m]),\qquad \alpha Q_y\preceq\nabla^2F(y)\preceq\alpha(2s+1)Q_y .
--   $$
--   4. **(d)** $m^{-1/(2s)}E_{G_*}\subseteq K_y\subseteq\big(m^{1-1/s}n^{1/s}\big)^{1/2}E_{G_*}$ and $\|B_h\|_{op}^2\le9\,Q_y[h,h]$.
--   5. **(e)** $\big\|G_*^{-1/2}\,\nabla G_*(y)[h]\,G_*^{-1/2}\big\|_F\le\sqrt{6\,\nabla^2F(y)[h,h]/\alpha}$.
--
--   The barrier parameter $\nu=O(m\log^2(2mn))$ is nearly linear in the number $m$ of dual variables, against $n$ for the logarithmic barrier $-\log\det S(y)$; this is what drives the faster SDP solver of Part II.
--
--   **Formalization Note** Part (b) is stated with the published platform predicate for a $\nu$-self-concordant barrier (barrier at every frontier point, convexity, $C^3$, the line form of the third-derivative bound and $\nabla F(y)[h]\le\sqrt{\nu\nabla^2F(y)[h,h]}$), and each printed clause of (b) is also stated explicitly with Fréchet derivatives. Smoothness of $G_*$ is entrywise $C^\infty$ on $\Omega$, $\nabla G_*(y)[h]$ is the entrywise derivative of $t\mapsto G_*(y+th)$ at $0$, and $(\nabla F(y))_i=\nabla F(y)[e_i]$.
--
--   Differences from the source:
--   - encoding: m a positive integer (Section 3.1) → hypothesis 0 < m; reason: excludes only m = 0, where s = 2⌈log(2mn)⌉ takes log 0; with m ≥ 1 the hypotheses force n ≥ 1
--   - encoding: Aᵢ, C ∈ Sⁿ, y, h ∈ ℝᵐ → real n×n matrices with IsHermitian hypotheses; y, h ∈ EuclideanSpace ℝ (Fin m); reason: Lean representation of the same objects
--   - encoding: G_*(y), the unique minimizer of f_y → optWeightAt / optWeight, a chosen minimizer (junk 0 if none exists); reason: by Lemma 4.4 the minimizer exists and is unique under (4.3), so the chosen one is G_*
--   - encoding: 'F is a ν-self-concordant barrier' (Definition 3.1) → EntropicBarrier.Universal.IsNuSelfConcordantBarrier Ω F ν together with the explicit clauses of (b); reason: the published predicate is Definition 3.1 without its positive-definite-Hessian clause, which (b) states separately; Ω is open, so interior Ω = Ω
--   - encoding: G_* depends smoothly on y; ∇G_*(y)[h]; (∇F(y))ᵢ; Loewner order of forms → entrywise ContDiffOn ℝ ∞ on Ω; entrywise deriv of t ↦ G_*(y + th) at 0; fderiv F y (eᵢ); pointwise inequalities of the forms for every h; reason: same quantities; entrywise derivatives avoid choosing a norm on matrices
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Theorem 2.1, pp.29–30

import Mathlib
import Definitions.Def_MatrixLeeSidford_barrierF
import Definitions.Def_MatrixLeeSidford_optWeightAt
import Definitions.Def_MatrixLeeSidford_Mmat
import Definitions.Def_MatrixLeeSidford_Qform
import Definitions.Def_MatrixLeeSidford_ellipsoid
import Definitions.Def_MatrixLeeSidford_localRegion
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_MatrixLeeSidford_matRpow
import Definitions.Def_LiqPremiaEq_opNorm
import Definitions.Def_MatrixLeeSidford_dualRegion
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **Theorem 2.1 (Matrix Lee–Sidford barrier)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), pp.29–30). Let `A₁, …, A_m, C ∈ Sⁿ` with
`Ω = {y : S(y) ≻ 0} ≠ ∅`, the `Aᵢ` linearly independent and `⋂ᵢ ker Aᵢ = {0}`. Let
`s := 2⌈log(2mn)⌉`, `α := 10⁶s²`, `ν := αm`, `F := αΦ_p`. For every `y ∈ Ω` and `h ∈ ℝᵐ`:
(a) the minimum in (2.1) is attained at a unique `G_* = G_*(y) ≻ 0`, smooth in `y`, with
`tr[L_y(G_*)^s] = m` and `Φ_p(y) = −½ log det G_* + m/(2s) − m/2`;
(b) `F` is a `ν`-self-concordant barrier for `Ω`: its Hessian is positive definite, `F` diverges at
every boundary point of `Ω`, `|∇³F(y)[h,h,h]| ≤ 2(∇²F(y)[h,h])^{3/2}`, `|∇F(y)[h]|² ≤ ν∇²F(y)[h,h]`;
(c) with `W_y := L_y(G_*)^{s−1}`, `M_y := ½(L_y(G_*)^s + ∑ (G_*)ᵢⱼ Bᵢ W_y Bⱼ)`, `Q_y[h,h] := tr[M_y B_h²]`:
`M_y ≻ 0`, `tr[M_y] = m`, `(∇F(y))ᵢ = −α tr[M_y Bᵢ]`, `αQ_y ⪯ ∇²F(y) ⪯ α(2s+1)Q_y`;
(d) `m^{−1/(2s)} E_{G_*} ⊆ K_y ⊆ (m^{1−1/s} n^{1/s})^{1/2} E_{G_*}` and `‖B_h‖_op² ≤ 9 Q_y[h,h]`;
(e) `‖G_*^{−1/2} ∇G_*(y)[h] G_*^{−1/2}‖_F ≤ √(6∇²F(y)[h,h]/α)`.

**Formalization Note** `m ≥ 1` (Section 3.1; at `m = 0` the formula for `s` takes `log 0`).
Part (b) uses the published `EntropicBarrier.Universal.IsNuSelfConcordantBarrier` (barrier at
every frontier point within the interior, convex and `C³` with the line form of
`|∇³F| ≤ 2(∇²F)^{3/2}`, and `∇F(y)[h] ≤ √(ν∇²F(y)[h,h])`) and also states each printed clause
of (b) explicitly with `iteratedFDeriv`/`fderiv`. Smoothness of `G_*` is entrywise `C^∞` on `Ω`;
`∇G_*(y)[h]` is the entrywise derivative of `t ↦ G_*(y + th)` at `0`; `(∇F(y))ᵢ` is
`∇F(y)[eᵢ]`. -/
theorem theorem_2_1 {n m : ℕ} (hm : 0 < m) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (hΩ : (dualRegion A C).Nonempty) (hlin : LinearIndependent ℝ A)
    (hker : ∀ v : Fin n → ℝ, (∀ i, A i *ᵥ v = 0) → v = 0) :
    let s := sParam m n
    let α := alphaParam s
    let F := barrierF A C
    let Ω := dualRegion A C
    -- (a)
    ((∀ y ∈ Ω, ∃! G : Matrix (Fin m) (Fin m) ℝ, G.PosDef ∧
        ∀ G' : Matrix (Fin m) (Fin m) ℝ, G'.PosDef → fObj A (slack A C y) s G ≤ fObj A (slack A C y) s G') ∧
      (∀ y ∈ Ω, (optWeightAt A C s y).PosDef ∧
        ∀ G' : Matrix (Fin m) (Fin m) ℝ, G'.PosDef →
          fObj A (slack A C y) s (optWeightAt A C s y) ≤ fObj A (slack A C y) s G') ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun y => optWeightAt A C s y i j) Ω) ∧
      (∀ y ∈ Ω, (Lmap A (slack A C y) (optWeightAt A C s y) ^ s).trace = m ∧
        Phi A C s y = -(1 / 2) * Real.log (optWeightAt A C s y).det + (m : ℝ) / (2 * (s : ℝ)) -
          (m : ℝ) / 2)) ∧
    -- (b)
    (EntropicBarrier.Universal.IsNuSelfConcordantBarrier Ω F (α * m) ∧
      (∀ y ∈ Ω, ∀ h : EuclideanSpace ℝ (Fin m), h ≠ 0 → 0 < iteratedFDeriv ℝ 2 F y (fun _ => h)) ∧
      (∀ ybar ∈ frontier Ω, Tendsto F (𝓝[Ω] ybar) atTop) ∧
      (∀ y ∈ Ω, ∀ h : EuclideanSpace ℝ (Fin m),
        |iteratedFDeriv ℝ 3 F y (fun _ => h)| ≤ 2 * (iteratedFDeriv ℝ 2 F y (fun _ => h)) ^ ((3 : ℝ) / 2) ∧
        |fderiv ℝ F y h| ^ 2 ≤ α * m * iteratedFDeriv ℝ 2 F y (fun _ => h))) ∧
    -- (c)
    (∀ y ∈ Ω, (Mmat A (slack A C y) s).PosDef ∧ (Mmat A (slack A C y) s).trace = m ∧
      (∀ i : Fin m, fderiv ℝ F y (EuclideanSpace.single i 1) =
        -α * (Mmat A (slack A C y) s * normB A (slack A C y) i).trace) ∧
      ∀ h : EuclideanSpace ℝ (Fin m),
        α * Qform A (slack A C y) s h ≤ iteratedFDeriv ℝ 2 F y (fun _ => h) ∧
        iteratedFDeriv ℝ 2 F y (fun _ => h) ≤ α * (2 * (s : ℝ) + 1) * Qform A (slack A C y) s h) ∧
    -- (d)
    (∀ y ∈ Ω,
      ((m : ℝ) ^ (-(1 / (2 * (s : ℝ))))) • ellipsoid (optWeightAt A C s y) ⊆ localRegion A (slack A C y) ∧
      localRegion A (slack A C y) ⊆
        (((m : ℝ) ^ (1 - 1 / (s : ℝ)) * (n : ℝ) ^ (1 / (s : ℝ))) ^ ((1 : ℝ) / 2)) •
          ellipsoid (optWeightAt A C s y) ∧
      ∀ h : EuclideanSpace ℝ (Fin m),
        LiqPremiaEq.opNorm (Bdir A (slack A C y) h) ^ 2 ≤ 9 * Qform A (slack A C y) s h) ∧
    -- (e)
    (∀ y ∈ Ω, ∀ h : EuclideanSpace ℝ (Fin m),
      let G := optWeightAt A C s y
      let DG : Matrix (Fin m) (Fin m) ℝ :=
        Matrix.of fun i j => deriv (fun t : ℝ => optWeightAt A C s (y + t • h) i j) 0
      LowRankMEG.frobNorm (matRpow (-(1 / 2)) G * DG * matRpow (-(1 / 2)) G) ≤
        Real.sqrt (6 * iteratedFDeriv ℝ 2 F y (fun _ => h) / α)) := by sorry

end MatrixLeeSidford
