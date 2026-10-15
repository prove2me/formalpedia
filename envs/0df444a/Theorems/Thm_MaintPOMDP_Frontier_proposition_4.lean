-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_proposition_4
-- name    : MaintPOMDP.Frontier.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:10.582929+00:00
-- url     : https://prove2.me/theorems/71a258f6-5a75-4ec5-aaae-6b8494419c22
-- title:
--   Proposition 4, p. 23 — f(m) has a unique local (and global) minimum on [0, ∞), f′ changes sign at most once, f′(m) → 0
-- statement:
--   Under the standing assumptions, assume $\gamma_0\ne\gamma_1$ and
--   $$c^R<\min\Big\{\frac{\gamma_0}{\gamma_1}\frac{c^P+\beta\gamma_1c^F}{1-\beta+\beta(\gamma_0+\gamma_1)},\ \frac{c^P+\beta\gamma_1c^F}{1-\beta+\beta(\gamma_0+\gamma_1)}\Big\}.$$
--   Read the closed form (31) of $f$ as a function of a real variable $m\ge0$ (with $\rho^{m+1}$ a real power). Then:
--   1. $f$ has a unique local minimum over $[0,\infty)$, and it is the global minimum over $[0,\infty)$;
--   2. the derivative $f'$ is either positive on $(0,\infty)$, or there is $m_1>0$ with $f'<0$ on $[0,m_1)$ and $f'>0$ on $(m_1,\infty)$;
--   3. $\lim_{m\to\infty}f'(m)=0$.
--
--   These properties make the integer minimizer $m^\dagger$ of Theorem 1 easy to locate.
--
--   **Formalization Note** The printed proposition has no hypotheses; its proof (EC pp. 9–11) assumes $\gamma_0\ne\gamma_1$ (the case $\gamma_0=\gamma_1$ is a separate proposition in App. B) and uses the displayed range of $c^R$ (the recurrent-replacement case of Theorem 1), so both are added. "Always positive" is stated on the open half-line $(0,\infty)$, leaving out the single point $m=0$.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), p. 23, Proposition 4; proof EC pp. 9–11

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Proposition 4 (p. 23), with the hypotheses its proof uses (γ0 ≠ γ1 and the [PR] range of
c^R): the closed form f(m) of (31), read on real m ≥ 0, has a unique local minimum on [0, ∞), which
is its global minimum; f′ is positive on (0, ∞) or changes sign once from negative to positive;
and f′(m) → 0 as m → ∞. -/
theorem proposition_4 (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1)
    (hcR : M.cR < min (M.γ0 / M.γ1 * M.thrP) M.thrP) :
    (∃ m0 : ℝ, 0 ≤ m0 ∧ IsMinOn M.f31R (Set.Ici 0) m0 ∧
        ∀ m : ℝ, 0 ≤ m → IsLocalMinOn M.f31R (Set.Ici 0) m → m = m0) ∧
      ((∀ m : ℝ, 0 < m → 0 < deriv M.f31R m) ∨
        ∃ m1 : ℝ, 0 < m1 ∧ (∀ m : ℝ, 0 ≤ m → m < m1 → deriv M.f31R m < 0) ∧
          ∀ m : ℝ, m1 < m → 0 < deriv M.f31R m) ∧
      Tendsto (deriv M.f31R) atTop (𝓝 0) := by sorry

end MaintPOMDP.Frontier
