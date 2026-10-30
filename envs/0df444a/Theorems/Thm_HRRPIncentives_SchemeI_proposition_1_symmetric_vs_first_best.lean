-- Prove2me | Theorems.Thm_HRRPIncentives_SchemeI_proposition_1_symmetric_vs_first_best
-- name    : HRRPIncentives.SchemeI.proposition_1_symmetric_vs_first_best
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:19:46.216983+00:00
-- url     : https://prove2.me/theorems/fb2f33dd-47de-48d0-9bd8-e8b956544a90
-- title:
--   Proposition 1 (second clause): symmetric equilibria have $\tilde r<r^*$, $\tilde c>c^*$
-- statement:
--   Throughout, $\lambda>0$ is the patients' arrival rate, the action box is $B=[r_{\min},r_{\max}]\times[c_{\min},c_{\max}]$, and the investment cost $R:B\to\mathbb R$ satisfies the standing assumptions of the paper (p. 10): $0<r_{\min}<r_{\max}<1$, $0\le c_{\min}<c_{\max}$, $R$ is non-increasing in each argument, jointly convex and twice differentiable on $B$, $R_{rr}R_{cc}>(R_{rc}+\lambda)^2$ and $R_{cr}\ge 0$ on $B$.
--
--   Let $N\ge2$ hospitals be paid by the HRRP-I transfer (9), and let $(r^*,c^*)$ be the first best: a maximizer of the social welfare $S(r,c)=V-c(1+r)\lambda-R(r,c)$ over $B$ lying in the open box, $r_{\min}<r^*<r_{\max}$ and $c_{\min}<c^*<c_{\max}$. Then every symmetric equilibrium $(\tilde r,\tilde c)$ satisfies
--
--   $$\tilde r<r^*\qquad\text{and}\qquad \tilde c>c^* .$$
--
--   Hospitals over-invest in readmission reduction and under-invest in cost reduction relative to the first best. This is the second of the three clauses of Proposition 1; the full proposition is the mission's goal.
--
--   Differences from the source:
--
--   - generalization: the standing assumptions include the additional boundary conditions of Appendix A that make optimal actions interior (p. 10) → those boundary conditions are not assumed; reason: Appendix A is not in the artifact; dropping hypotheses only enlarges the class of cost functions R, so the statement specializes to the source's
--   - generalization: R(r, c) is decreasing in r and c → R is antitone (non-increasing) in each argument on the box; reason: the non-strict reading is the weaker hypothesis; every decreasing R satisfies it
--   - reading: patients arrive at each hospital at a fixed rate λ (p. 9) → 0 < λ; reason: λ is an arrival rate; with λ = 0 the claims r̃ < r*, c̃ > c* fail
--   - encoding: 0 < r_min ≤ r_max < 1 → 0 < r_min < r_max < 1; reason: Lemma 1 (p. 11) places r* in the open interval (r_min, r_max), so the source's assumptions already exclude r_min = r_max; the nonempty interior makes derivatives within the box unique
--   - encoding: R is twice differentiable; R_x denotes the partial derivative in x → R and its derivative are differentiable within the closed box; partials are derivatives within the box along (1,0) and (0,1); R_rc = ∂_c(∂_r R) and R_cr = ∂_r(∂_c R) in the printed order; reason: R is only defined on the box, so derivatives are taken within it; no continuity of the second derivative and no extension beyond the box are assumed
--   - encoding: N hospitals, with yardsticks averaging over the other N − 1 (6) → 2 ≤ N; reason: implicit in the factor 1/(N − 1) of (6)
--   - generalization: (r*, c*) is the first best of Lemma 1, which under the Appendix A conditions is the unique maximizer of S and lies in (r_min, r_max) × (c_min, c_max) → clause (b) assumes of (r*, c*) only that it maximizes S on the box and lies in the open box; reason: Appendix A is not in the artifact; Lemma 1 derives exactly this interiority from it, so every instance of the source satisfies the premise
--   - reading: r̃ < r*, c̃ > c* for Lemma 1's (r*, c*) → for every interior maximizer (r*, c*) of S on the box; reason: S has exactly one maximizer under the standing assumptions (footnote 6), so the quantifier ranges over the single first best
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, Proposition 1 (second clause), p. 14; (r*, c*) as in Lemma 1, p. 11

import Mathlib
import Definitions.Def_HRRPIncentives_SchemeI_Standing
import Definitions.Def_HRRPIncentives_SchemeI_welfare
import Definitions.Def_HRRPIncentives_SchemeI_IsEquilibrium

namespace HRRPIncentives.SchemeI

/-- Proposition 1, second clause: under HRRP-I, for every `N ≥ 2`, every symmetric equilibrium
`(r̃, c̃)` satisfies `r̃ < r*` and `c̃ > c*`, where `(r*, c*)` is the first best: the maximizer
of social welfare (2) on the box, which lies in the open box `(rmin, rmax) × (cmin, cmax)`.

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, Proposition 1 (second clause), p. 14; `(r*, c*)` as in Lemma 1, p. 11.

**Formalization Note.** Appendix A's boundary conditions (not in the artifact) are dropped from
the standing assumptions. The only consequence of them used here, the interiority of the first
best from Lemma 1, is assumed for `q = (r*, c*)` instead. No interiority is assumed for the
equilibrium. `V` is the constant `V(λ)`; it does not affect the maximizer. -/
theorem proposition_1_symmetric_vs_first_best {lam rmin rmax cmin cmax : ℝ} (V : ℝ)
    {R : ℝ × ℝ → ℝ} (hR : Standing lam rmin rmax cmin cmax R) {N : ℕ} (hN : 2 ≤ N)
    (p q : ℝ × ℝ) (hp : IsEquilibrium lam rmin rmax cmin cmax R (fun _ : Fin N => p))
    (hq : q ∈ box rmin rmax cmin cmax)
    (hqmax : IsMaxOn (welfare lam V R) (box rmin rmax cmin cmax) q)
    (hq1 : rmin < q.1) (hq1' : q.1 < rmax) (hq2 : cmin < q.2) (hq2' : q.2 < cmax) :
    p.1 < q.1 ∧ q.2 < p.2 := by sorry

end HRRPIncentives.SchemeI
