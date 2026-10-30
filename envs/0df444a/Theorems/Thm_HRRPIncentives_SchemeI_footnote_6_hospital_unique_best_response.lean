-- Prove2me | Theorems.Thm_HRRPIncentives_SchemeI_footnote_6_hospital_unique_best_response
-- name    : HRRPIncentives.SchemeI.footnote_6_hospital_unique_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:17:54.245407+00:00
-- url     : https://prove2.me/theorems/8f88c7b0-8d35-4fe3-8b30-127dfb287c44
-- title:
--   Footnote 6: the HRRP-I hospital objective has a unique maximizer
-- statement:
--   Throughout, $\lambda>0$ is the patients' arrival rate, the action box is $B=[r_{\min},r_{\max}]\times[c_{\min},c_{\max}]$, and the investment cost $R:B\to\mathbb R$ satisfies the standing assumptions of the paper (p. 10): $0<r_{\min}<r_{\max}<1$, $0\le c_{\min}<c_{\max}$, $R$ is non-increasing in each argument, jointly convex and twice differentiable on $B$, $R_{rr}R_{cc}>(R_{rc}+\lambda)^2$ and $R_{cr}\ge 0$ on $B$.
--
--   Let $N\ge2$, fix the actions $(r_k,c_k)\in B$ of the hospitals $k\ne i$, and let hospital $i$ be paid the HRRP-I transfer (9), whose yardsticks $\bar c_i,\bar r_i,\bar R_i$ are computed from those actions. Then hospital $i$'s objective
--
--   $$(r,c)\mapsto \bar c_i\lambda(1+r)-\frac{1}{\bar r_i}(r-\bar r_i)(1+r)\bar c_i\lambda+\bar R_i-c(1+r)\lambda-R(r,c)$$
--
--   has exactly one maximizer over $B$. In other words, every hospital has a unique best response to the others' actions.
--
--   Differences from the source:
--
--   - generalization: the standing assumptions include the additional boundary conditions of Appendix A that make optimal actions interior (p. 10) → those boundary conditions are not assumed; reason: Appendix A is not in the artifact; dropping hypotheses only enlarges the class of cost functions R, so the statement specializes to the source's
--   - generalization: R(r, c) is decreasing in r and c → R is antitone (non-increasing) in each argument on the box; reason: the non-strict reading is the weaker hypothesis; every decreasing R satisfies it
--   - reading: patients arrive at each hospital at a fixed rate λ (p. 9) → 0 < λ; reason: λ is an arrival rate; with λ = 0 the claims r̃ < r*, c̃ > c* fail
--   - encoding: 0 < r_min ≤ r_max < 1 → 0 < r_min < r_max < 1; reason: Lemma 1 (p. 11) places r* in the open interval (r_min, r_max), so the source's assumptions already exclude r_min = r_max; the nonempty interior makes derivatives within the box unique
--   - encoding: R is twice differentiable; R_x denotes the partial derivative in x → R and its derivative are differentiable within the closed box; partials are derivatives within the box along (1,0) and (0,1); R_rc = ∂_c(∂_r R) and R_cr = ∂_r(∂_c R) in the printed order; reason: R is only defined on the box, so derivatives are taken within it; no continuity of the second derivative and no extension beyond the box are assumed
--   - encoding: N hospitals, with yardsticks averaging over the other N − 1 (6) → 2 ≤ N; reason: implicit in the factor 1/(N − 1) of (6)
--   - reading: objective functions of the … hospitals are unimodal → the hospital objective (1) under the HRRP-I transfer (9); reason: Proposition 1 concerns HRRP-I; the footnote names no scheme
--   - generalization: all hospitals' actions lie in the box → only the other hospitals' actions are required to lie in the box; reason: hospital i's own current action does not enter its objective as a function of the deviation
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, footnote 6, p. 10 (hospital half), for the HRRP-I transfer (9), p. 14

import Mathlib
import Definitions.Def_HRRPIncentives_SchemeI_Standing
import Definitions.Def_HRRPIncentives_SchemeI_payoff

namespace HRRPIncentives.SchemeI

/-- Under the standing assumptions and the HRRP-I transfer (9), each hospital's objective (1),
as a function of its own action with the other hospitals' actions fixed in the box, has exactly
one maximizer on the action box.

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, footnote 6, p. 10 ("This assumption is just a sufficient condition that ensures
that objective functions of the regulator and hospitals are unimodal (i.e. have unique
maximums)"), the hospital half, for the HRRP-I scheme of display (9), p. 14.

**Formalization Note.** Footnote 6's "hospitals" is read as the hospital objective under
HRRP-I, the scheme of Proposition 1. The own action `x i` is replaced by `y` via
`Function.update`; only the other hospitals' actions are required to lie in the box (the
yardsticks (6) of hospital `i` do not involve `x i`). `N ≥ 2` is implicit in the
`1/(N−1)` of (6). -/
theorem footnote_6_hospital_unique_best_response {lam rmin rmax cmin cmax : ℝ}
    {R : ℝ × ℝ → ℝ} (hR : Standing lam rmin rmax cmin cmax R) {N : ℕ} (hN : 2 ≤ N)
    (x : Fin N → ℝ × ℝ) (i : Fin N) (hx : ∀ k, k ≠ i → x k ∈ box rmin rmax cmin cmax) :
    ∃! y, y ∈ box rmin rmax cmin cmax ∧
      IsMaxOn (fun y => payoff lam R (Function.update x i y) i)
        (box rmin rmax cmin cmax) y := by sorry

end HRRPIncentives.SchemeI
