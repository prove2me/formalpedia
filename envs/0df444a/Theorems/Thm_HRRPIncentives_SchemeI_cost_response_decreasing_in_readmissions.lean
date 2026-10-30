-- Prove2me | Theorems.Thm_HRRPIncentives_SchemeI_cost_response_decreasing_in_readmissions
-- name    : HRRPIncentives.SchemeI.cost_response_decreasing_in_readmissions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:18:21.127493+00:00
-- url     : https://prove2.me/theorems/871cb86d-3a27-4b23-85f4-c33f1435c079
-- title:
--   Unnumbered (p. 14): the cost choice decreases in the readmission rate
-- statement:
--   Throughout, $\lambda>0$ is the patients' arrival rate, the action box is $B=[r_{\min},r_{\max}]\times[c_{\min},c_{\max}]$, and the investment cost $R:B\to\mathbb R$ satisfies the standing assumptions of the paper (p. 10): $0<r_{\min}<r_{\max}<1$, $0\le c_{\min}<c_{\max}$, $R$ is non-increasing in each argument, jointly convex and twice differentiable on $B$, $R_{rr}R_{cc}>(R_{rc}+\lambda)^2$ and $R_{cr}\ge 0$ on $B$.
--
--   Let $r<r'$ be readmission rates in $[r_{\min},r_{\max}]$. Let $c$ maximize $c\mapsto -c(1+r)\lambda-R(r,c)$ over $[c_{\min},c_{\max}]$ and let $c'$ maximize $c\mapsto -c(1+r')\lambda-R(r',c)$ over $[c_{\min},c_{\max}]$. Then
--
--   $$c'\le c,$$
--
--   and $c'<c$ whenever $c$ or $c'$ lies in the open interval $(c_{\min},c_{\max})$.
--
--   A hospital's own cost $c$ enters its objective (1) only through $-c(1+r)\lambda-R(r,c)$, since the transfer (9) does not depend on it. So this is the mechanism the paper gives after Proposition 1: a hospital with a lower readmission rate treats fewer visits $(1+r)\lambda$, gains less from reducing its marginal cost, and therefore chooses a higher cost.
--
--   Differences from the source:
--
--   - generalization: the standing assumptions include the additional boundary conditions of Appendix A that make optimal actions interior (p. 10) → those boundary conditions are not assumed; reason: Appendix A is not in the artifact; dropping hypotheses only enlarges the class of cost functions R, so the statement specializes to the source's
--   - generalization: R(r, c) is decreasing in r and c → R is antitone (non-increasing) in each argument on the box; reason: the non-strict reading is the weaker hypothesis; every decreasing R satisfies it
--   - reading: patients arrive at each hospital at a fixed rate λ (p. 9) → 0 < λ; reason: λ is an arrival rate; with λ = 0 the claims r̃ < r*, c̃ > c* fail
--   - encoding: 0 < r_min ≤ r_max < 1 → 0 < r_min < r_max < 1; reason: Lemma 1 (p. 11) places r* in the open interval (r_min, r_max), so the source's assumptions already exclude r_min = r_max; the nonempty interior makes derivatives within the box unique
--   - encoding: R is twice differentiable; R_x denotes the partial derivative in x → R and its derivative are differentiable within the closed box; partials are derivatives within the box along (1,0) and (0,1); R_rc = ∂_c(∂_r R) and R_cr = ∂_r(∂_c R) in the printed order; reason: R is only defined on the box, so derivatives are taken within it; no continuity of the second derivative and no extension beyond the box are assumed
--   - reading: over-investment in readmission reduction leads to under-investment in cost-reduction efforts because the total number of admissions is lower and so the total benefit of reducing marginal cost is lower → the maximizer in c of −c(1+r)λ − R(r,c) on [c_min, c_max] is non-increasing in r, strictly when either maximizer is interior; reason: the passage is a verbal comparative static; this is its precise form, in argmax form because the function h of (5) needs Appendix A to be well defined
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, unnumbered, p. 14, paragraph after Proposition 1; compare the remark after display (5), p. 11

import Mathlib
import Definitions.Def_HRRPIncentives_SchemeI_Standing

namespace HRRPIncentives.SchemeI

/-- Under the standing assumptions, the cost-reduction choice is decreasing in the readmission
rate: if `r < r'` in `[rmin, rmax]`, `c` maximizes `−c(1 + r)λ − R(r, c)` over
`[cmin, cmax]` and `c'` maximizes `−c(1 + r')λ − R(r', c)` over `[cmin, cmax]`, then
`c' ≤ c`, and `c' < c` as soon as `c` or `c'` lies in the open interval `(cmin, cmax)`.

A hospital's marginal cost `c` enters its objective (1) only through `−c(1 + r)λ − R(r, c)`
(the transfer (9) does not depend on its own `c`), so this is the comparative static of the
hospital's cost choice: fewer total visits `(1 + r)λ` give a lower benefit of reducing `c`.

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, unnumbered, p. 14, paragraph after Proposition 1 ("over-investment in readmission
reduction leads to under-investment in cost-reduction efforts (i.e., c̃ > c*), relative to
first-best, because in equilibrium the total number of admissions … is lower …, and so the total
benefit of reducing marginal cost is lower"). Compare the remark after (5), p. 11 (`h` is
decreasing in `r`), here in argmax form.

**Formalization Note.** The argmax form is used because the "well defined" part of the remark
after (5) relies on Appendix A, which is not in the artifact. -/
theorem cost_response_decreasing_in_readmissions {lam rmin rmax cmin cmax : ℝ}
    {R : ℝ × ℝ → ℝ} (hR : Standing lam rmin rmax cmin cmax R) {r r' c c' : ℝ}
    (hr : r ∈ Set.Icc rmin rmax) (hr' : r' ∈ Set.Icc rmin rmax) (hrr' : r < r')
    (hc : c ∈ Set.Icc cmin cmax) (hc' : c' ∈ Set.Icc cmin cmax)
    (hmax : IsMaxOn (fun c => -(c * (1 + r) * lam) - R (r, c)) (Set.Icc cmin cmax) c)
    (hmax' : IsMaxOn (fun c => -(c * (1 + r') * lam) - R (r', c)) (Set.Icc cmin cmax) c') :
    c' ≤ c ∧ (c ∈ Set.Ioo cmin cmax ∨ c' ∈ Set.Ioo cmin cmax → c' < c) := by sorry

end HRRPIncentives.SchemeI
