-- Prove2me | Theorems.Thm_GuthMaynard_mu_half_le_twentyseven_div_onesixtyfour
-- name    : GuthMaynard.mu_half_le_twentyseven_div_onesixtyfour
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-14T21:40:35.060379+00:00
-- url     : https://prove2.me/theorems/cb56729b-b646-49a3-aa16-63cf0eee7653
-- title:
--   Sub-Weyl bound μ(1/2) ≤ 27/164 for ζ on the critical line
-- statement:
--   $$\mu(\tfrac12) \le \tfrac{27}{164},$$
--   where $\mu(\sigma)$ is `LindelofHypothesis.mu σ`: the infimum of the real $a$ with $\zeta(\sigma + iT) = O(T^a)$ as $T \to +\infty$. So the statement says that $\zeta(\tfrac12 + iT) = O(T^{a})$ for every $a > 27/164$.
--
--   The exponent $27/164 = 0.1646\ldots$ lies just below Weyl's $1/6$. It is the exponent of D. Patel and A. Yang, *An explicit sub-Weyl bound for $\zeta(1/2+it)$*, arXiv:2302.13444, https://arxiv.org/abs/2302.13444, whose abstract states the bound $|\zeta(1/2+it)| \le 66.7\,t^{27/164}$ for $t \ge 3$; that explicit inequality implies this statement, which keeps only the exponent. The exponent comes from van der Corput's method: with the exponent pair $(\kappa, \lambda) = (11/82, 57/82)$, which is $ABA^3B(0,1)$, one has $\mu(\tfrac12) \le (\kappa + \lambda - \tfrac12)/2 = 27/164$.
--
--   It is published here because it suffices, in place of Haneke's bound, for the range $\alpha \ge 9/11$ of Huxley's zero-density estimate (`GuthMaynard.huxley_density_estimate_of_nine_elevenths_le`): any exponent below $1/6$ serves there.
--
--   **Formalization note.**
--   - Only the exponent is stated; no explicit constant and no range of $t$.
--   - `LindelofHypothesis.mu` is an infimum in the extended reals, so the statement does not assert that $\zeta(\tfrac12+iT) = O(T^{27/164})$ itself.
-- source:
--   Patel, D. and Yang, A., An explicit sub-Weyl bound for ζ(1/2+it), arXiv:2302.13444 (2023), https://arxiv.org/abs/2302.13444, p. 1, the exponent 27/164 of the abstract and the introduction (the explicit constant is not stated here), used in place of Haneke's bound (6.7) in Huxley (1.9), α ≥ 9/11 (Invent. Math. 15 (1972), p. 169)

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

namespace GuthMaynard

theorem mu_half_le_twentyseven_div_onesixtyfour :
    LindelofHypothesis.mu (1 / 2) ≤ ((27 / 164 : ℝ) : EReal) := by
  sorry

end GuthMaynard
