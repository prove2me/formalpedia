-- Prove2me | Theorems.Thm_MuonLastIterate110_Stochastic_lemma_3_2
-- name    : MuonLastIterate110.Stochastic.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:59:21.62274+00:00
-- url     : https://prove2.me/theorems/7cce3e09-d977-488a-be75-77f70ca3ae30
-- title:
--   Lemma 3.2 — finite Newton–Schulz bounds and alignment
-- statement:
--   Fix a finite $J\ge1$ and let $\ell_J,u_J$ be the minimum and maximum of the amplification factor $q_J$ on $[0,1]$. Then the minimum and maximum are attained and
--
--   $$
--   0<\ell_J\le u_J<\infty .
--   $$
--
--   Moreover, for every $\varepsilon\ge0$ and every real matrix $N$, with $R=\|N\|_F$,
--
--   $$
--   \ell_J\frac{R}{R+\varepsilon}\le\|\Phi_\varepsilon(N)\|_F\le u_J\frac{R}{R+\varepsilon}\le u_J,\qquad
--   \langle N,\Phi_\varepsilon(N)\rangle_F\ge\ell_J\frac{R^2}{R+\varepsilon},
--   $$
--
--   and, if $\varepsilon>0$,
--
--   $$
--   \langle N,\Phi_\varepsilon(N)\rangle_F\ge\frac{\varepsilon}{u_J}\|\Phi_\varepsilon(N)\|_F^2 .
--   $$
--
--   When $R=\varepsilon=0$ the fractions are zero.
--
--   These radial and alignment bounds hold for every finite number of Newton–Schulz steps and are the only properties of $\Phi_\varepsilon$ used in the convergence analysis; in particular $\|D_t\|\le B=u_J$.
--
--   **Formalization Note** The fractions use Lean's division, which is $0$ at $R=\varepsilon=0$, as the source stipulates.
--
--   Differences from the source:
--
--   - encoding: ℓ_J = min and u_J = max of q_J on [0,1]; 0 < ℓ_J ≤ u_J < ∞ → ℓ_J, u_J are sInf/sSup of q_J([0,1]), and the theorem asserts they are attained (IsLeast, IsGreatest) together with 0 < ℓ_J ≤ u_J; reason: a real sSup carries no finiteness information; attainment is what min/max and u_J < ∞ say
--   - encoding: real m×n matrices with Frobenius norm ‖X‖_F and inner product tr(XᵀY) → EuclideanSpace ℝ (Fin m × Fin n), read as a matrix through toMat for the products of (3.4); reason: the Euclidean norm and inner product on this type are exactly the Frobenius ones (checked in the sanity file); same instances
-- source:
--   Ping Li and Vincent Y. F. Tan, Last-Iterate Stationarity of Muon with Finitely Many Newton-Schulz Iterations, STOC 2027 submission #110 preprint (2026), source.pdf SHA-256 5362e7185a9ddcba39d1a70da110a8b04f1d179ad818e6d5d0ec73bf29586372, p.6, Lemma 3.2, (3.6)–(3.8); proof p.14, Appendix A.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/110.pdf

import Mathlib
import Definitions.Def_MuonLastIterate110_Stochastic_NewtonSchulz

open scoped RealInnerProductSpace

namespace MuonLastIterate110.Stochastic

/-- Lemma 3.2 (Finite-NS bounds and alignment), p.6. For every finite `J ≥ 1` the minimum `ℓ_J`
and the maximum `u_J` of `q_J` on `[0,1]` are attained and `0 < ℓ_J ≤ u_J`; and for every
`ε ≥ 0` and every real `m × n` matrix `N` with `R = ‖N‖_F`, (3.6), (3.7) and, if `ε > 0`, (3.8)
hold. Fractions at `R = ε = 0` are `0` (Lean's division by zero), as the source stipulates. -/
theorem lemma_3_2 (J : ℕ) (hJ : 1 ≤ J) :
    (IsLeast (q J '' Set.Icc 0 1) (ellJ J) ∧ IsGreatest (q J '' Set.Icc 0 1) (uJ J) ∧
      0 < ellJ J ∧ ellJ J ≤ uJ J) ∧
    ∀ (m n : ℕ) (ε : ℝ), 0 ≤ ε → ∀ N : Mat m n,
      ellJ J * (‖N‖ / (‖N‖ + ε)) ≤ ‖Phi J ε N‖ ∧
      ‖Phi J ε N‖ ≤ uJ J * (‖N‖ / (‖N‖ + ε)) ∧
      uJ J * (‖N‖ / (‖N‖ + ε)) ≤ uJ J ∧
      ellJ J * (‖N‖ ^ 2 / (‖N‖ + ε)) ≤ ⟪N, Phi J ε N⟫ ∧
      (0 < ε → ε / uJ J * ‖Phi J ε N‖ ^ 2 ≤ ⟪N, Phi J ε N⟫) := by sorry

end MuonLastIterate110.Stochastic
