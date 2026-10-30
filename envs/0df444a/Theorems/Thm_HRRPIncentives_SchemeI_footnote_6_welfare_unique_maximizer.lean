-- Prove2me | Theorems.Thm_HRRPIncentives_SchemeI_footnote_6_welfare_unique_maximizer
-- name    : HRRPIncentives.SchemeI.footnote_6_welfare_unique_maximizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:16:56.88998+00:00
-- url     : https://prove2.me/theorems/e73b1501-0a05-4100-8d3c-5a0a270e1827
-- title:
--   Footnote 6: social welfare has a unique maximizer
-- statement:
--   Throughout, $\lambda>0$ is the patients' arrival rate, the action box is $B=[r_{\min},r_{\max}]\times[c_{\min},c_{\max}]$, and the investment cost $R:B\to\mathbb R$ satisfies the standing assumptions of the paper (p. 10): $0<r_{\min}<r_{\max}<1$, $0\le c_{\min}<c_{\max}$, $R$ is non-increasing in each argument, jointly convex and twice differentiable on $B$, $R_{rr}R_{cc}>(R_{rc}+\lambda)^2$ and $R_{cr}\ge 0$ on $B$.
--
--   Then for every constant $V$, the social welfare $S(r,c)=V-c(1+r)\lambda-R(r,c)$ has exactly one maximizer over the box $B$: there is a unique $q\in B$ with
--
--   $$S(q)=\max_{x\in B}S(x).$$
--
--   This is the regulator half of the paper's remark that the sufficient-convexity assumption makes the objectives unimodal. Its maximizer is the first best $(r^*,c^*)$; that it is interior (Lemma 1) is not claimed here, because it depends on the paper's Appendix A.
--
--   Differences from the source:
--
--   - generalization: the standing assumptions include the additional boundary conditions of Appendix A that make optimal actions interior (p. 10) → those boundary conditions are not assumed; reason: Appendix A is not in the artifact; dropping hypotheses only enlarges the class of cost functions R, so the statement specializes to the source's
--   - generalization: R(r, c) is decreasing in r and c → R is antitone (non-increasing) in each argument on the box; reason: the non-strict reading is the weaker hypothesis; every decreasing R satisfies it
--   - reading: patients arrive at each hospital at a fixed rate λ (p. 9) → 0 < λ; reason: λ is an arrival rate; with λ = 0 the claims r̃ < r*, c̃ > c* fail
--   - encoding: 0 < r_min ≤ r_max < 1 → 0 < r_min < r_max < 1; reason: Lemma 1 (p. 11) places r* in the open interval (r_min, r_max), so the source's assumptions already exclude r_min = r_max; the nonempty interior makes derivatives within the box unique
--   - encoding: R is twice differentiable; R_x denotes the partial derivative in x → R and its derivative are differentiable within the closed box; partials are derivatives within the box along (1,0) and (0,1); R_rc = ∂_c(∂_r R) and R_cr = ∂_r(∂_c R) in the printed order; reason: R is only defined on the box, so derivatives are taken within it; no continuity of the second derivative and no extension beyond the box are assumed
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, footnote 6, p. 10 (regulator half)

import Mathlib
import Definitions.Def_HRRPIncentives_SchemeI_Standing
import Definitions.Def_HRRPIncentives_SchemeI_welfare

namespace HRRPIncentives.SchemeI

/-- Under the standing assumptions, the regulator's objective, social welfare (2)
`S(r, c) = V(λ) − c(1 + r)λ − R(r, c)`, has exactly one maximizer on the action box.

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, footnote 6, p. 10 ("This assumption is just a sufficient condition that ensures
that objective functions of the regulator and hospitals are unimodal (i.e. have unique
maximums)"), the regulator half.

**Formalization Note.** Interiority of the maximizer (Lemma 1, p. 11) is not claimed: it rests
on the boundary conditions of Appendix A, which is not in the artifact. -/
theorem footnote_6_welfare_unique_maximizer {lam rmin rmax cmin cmax : ℝ} (V : ℝ)
    {R : ℝ × ℝ → ℝ} (hR : Standing lam rmin rmax cmin cmax R) :
    ∃! q, q ∈ box rmin rmax cmin cmax ∧
      IsMaxOn (welfare lam V R) (box rmin rmax cmin cmax) q := by sorry

end HRRPIncentives.SchemeI
