-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_corollary_4_4
-- name    : MultiSpinCounting.Positive.corollary_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:48.692028+00:00
-- url     : https://prove2.me/theorems/3832921c-0bed-4ed6-a74d-dc94cb3d87d2
-- title:
--   Corollary 4.4 — polytope diameter and multiplicative accuracy
-- statement:
--   Fix $K\ge1$, $\alpha\ge0$, $D\ge1$ and $0<c<1/D$, and put $\rho=Dc$, $\bar\Delta=4\operatorname{arctanh}c$. Let $\Phi$ be positive rational with $q\ge3$, $S_\ell(G)\le KN^\alpha D^\ell$ for all $\ell$, $N\ge1$, and $c_B(A_e)\le c$ on every edge. For $P\ge3$ and every $R\ge0$,
--   $$\operatorname{diam}_H\mathcal P_R(\Phi,v)\le KN^\alpha D\left(\bar\Delta\rho^R+\frac{2\xi_P}{1-\rho}\right).$$
--   For $0<\varepsilon<1$, define
--   $$R_\varepsilon=\left\lceil\frac{\log(4KN^\alpha D\max\{1,\bar\Delta\}/\varepsilon)}{\log(1/\rho)}\right\rceil,\qquad P_\varepsilon=\max\left\{3,\left\lceil\log_2\frac{32KN^\alpha D}{\varepsilon(1-\rho)}\right\rceil\right\}.$$
--   Whenever $R'\ge R_\varepsilon$, $P'\ge P_\varepsilon$, and $z\in\mathcal P_{R'}(\Phi,v)$ at precision $P'$, every spin $a$ satisfies
--   $$e^{-\varepsilon}\mu_\Phi(v\leftarrow a)\le z_a\le e^\varepsilon\mu_\Phi(v\leftarrow a).$$
--   The fixed $c$ also applies to edgeless derived instances and zero Birkhoff coefficients. This quantitative statement supplies both clauses of the corollary.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and spin sets → Fin n and Fin q, with an active vertex subset; reason: relabeling preserves every instance; active subsets implement the source sub-instances and the fixed vertex order
--   - generalization: n is the graph size and R,P equal the ceilings in (4.6) → any N ≥ 1 satisfying the walk bound, and any larger depth and precision; reason: taking N equal to the graph size and equality recovers the printed corollary; p. 17 uses exactly this ambient-size and larger-parameter form
--   - encoding: diameter and integer ceilings on their defined domains → an attained bounded real supremum and natural ceilings; reason: positive query data and 0 < Dc < 1 ensure the same real expressions and nonnegative ceilings
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), pp. 16–17, Corollary 4.4, (4.5), (4.6) and §4.2 use

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Polytopes

namespace MultiSpinCounting.Positive

/-- Corollary 4.4, p. 16, and its use with larger R,P and original ambient size on p. 17. -/
theorem corollary_4_4 {n q : ℕ} (hq : 3 ≤ q) (N : ℕ) (hN : 1 ≤ N)
    (K α D c : ℝ) (hK : 1 ≤ K) (hα : 0 ≤ α) (hD : 1 ≤ D)
    (hc : 0 < c) (hDc : D*c < 1) (Φ : Instance n q ℚ) (hΦ : IsPositive Φ)
    (hw : WalkBound Φ N K α D)
    (hcoeff : ∀ e ∈ edges Φ, cB ((realInstance Φ).interaction e.1 e.2) ≤ c)
    (v : Fin n) (hv : v ∈ Φ.active) (R P : ℕ) (hP : 3 ≤ P) :
    PolyWellDefined (polytope P R Φ v) ∧
    hilbertDiameter (polytope P R Φ v) ≤ K*(N:ℝ)^α*D *
      (4*Real.artanh c*(D*c)^R + 2*roundingAccuracy P/(1-D*c)) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ R' P' : ℕ,
      accuracyDepth N K α D c ε ≤ R' → accuracyPrecision N K α D c ε ≤ P' →
      ∀ z ∈ polytope P' R' Φ v, ∀ a : Fin q,
        Real.exp (-ε)*marginal (realInstance Φ) v a ≤ z a ∧
        z a ≤ Real.exp ε*marginal (realInstance Φ) v a) := by sorry

end MultiSpinCounting.Positive
