-- Prove2me | Theorems.Thm_HRRPIncentives_SchemeI_proposition_1_symmetric_existence
-- name    : HRRPIncentives.SchemeI.proposition_1_symmetric_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:19:15.021167+00:00
-- url     : https://prove2.me/theorems/05f76d43-4025-4b1d-aaf8-cf2364dd2b8e
-- title:
--   Proposition 1 (first clause): a symmetric HRRP-I equilibrium exists
-- statement:
--   Throughout, $\lambda>0$ is the patients' arrival rate, the action box is $B=[r_{\min},r_{\max}]\times[c_{\min},c_{\max}]$, and the investment cost $R:B\to\mathbb R$ satisfies the standing assumptions of the paper (p. 10): $0<r_{\min}<r_{\max}<1$, $0\le c_{\min}<c_{\max}$, $R$ is non-increasing in each argument, jointly convex and twice differentiable on $B$, $R_{rr}R_{cc}>(R_{rc}+\lambda)^2$ and $R_{cr}\ge 0$ on $B$.
--
--   Then for every number $N\ge2$ of hospitals paid by the HRRP-I transfer (9), there is a pair $(\tilde r,\tilde c)\in B$ such that all hospitals choosing $(\tilde r,\tilde c)$ is a pure-strategy Nash equilibrium:
--
--   $$\exists(\tilde r,\tilde c)\in B:\quad \big((\tilde r,\tilde c),\dots,(\tilde r,\tilde c)\big)\ \text{is an equilibrium}.$$
--
--   This is the first of the three clauses of Proposition 1; the full proposition is the mission's goal.
--
--   Differences from the source:
--
--   - generalization: the standing assumptions include the additional boundary conditions of Appendix A that make optimal actions interior (p. 10) → those boundary conditions are not assumed; reason: Appendix A is not in the artifact; dropping hypotheses only enlarges the class of cost functions R, so the statement specializes to the source's
--   - generalization: R(r, c) is decreasing in r and c → R is antitone (non-increasing) in each argument on the box; reason: the non-strict reading is the weaker hypothesis; every decreasing R satisfies it
--   - reading: patients arrive at each hospital at a fixed rate λ (p. 9) → 0 < λ; reason: λ is an arrival rate; with λ = 0 the claims r̃ < r*, c̃ > c* fail
--   - encoding: 0 < r_min ≤ r_max < 1 → 0 < r_min < r_max < 1; reason: Lemma 1 (p. 11) places r* in the open interval (r_min, r_max), so the source's assumptions already exclude r_min = r_max; the nonempty interior makes derivatives within the box unique
--   - encoding: R is twice differentiable; R_x denotes the partial derivative in x → R and its derivative are differentiable within the closed box; partials are derivatives within the box along (1,0) and (0,1); R_rc = ∂_c(∂_r R) and R_cr = ∂_r(∂_c R) in the printed order; reason: R is only defined on the box, so derivatives are taken within it; no continuity of the second derivative and no extension beyond the box are assumed
--   - encoding: N hospitals, with yardsticks averaging over the other N − 1 (6) → 2 ≤ N; reason: implicit in the factor 1/(N − 1) of (6)
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, Proposition 1 (first clause), p. 14

import Mathlib
import Definitions.Def_HRRPIncentives_SchemeI_Standing
import Definitions.Def_HRRPIncentives_SchemeI_IsEquilibrium

namespace HRRPIncentives.SchemeI

/-- Proposition 1, first clause: under HRRP-I, for every number `N ≥ 2` of hospitals there
exists a symmetric pure-strategy Nash equilibrium, i.e. a pair `(r̃, c̃)` in the box such that
all hospitals playing `(r̃, c̃)` is an equilibrium.

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, Proposition 1 (first clause), p. 14.

**Formalization Note.** Appendix A's boundary conditions are not assumed (not in the artifact);
see `Standing`. Equilibrium is a genuine Nash equilibrium (deviations over the whole box). -/
theorem proposition_1_symmetric_existence {lam rmin rmax cmin cmax : ℝ}
    {R : ℝ × ℝ → ℝ} (hR : Standing lam rmin rmax cmin cmax R) {N : ℕ} (hN : 2 ≤ N) :
    ∃ p ∈ box rmin rmax cmin cmax,
      IsEquilibrium lam rmin rmax cmin cmax R (fun _ : Fin N => p) := by sorry

end HRRPIncentives.SchemeI
