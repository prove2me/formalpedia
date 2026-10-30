-- Prove2me | Theorems.Thm_HRRPIncentives_SchemeI_proposition_1_hrrp_i_equilibrium
-- name    : HRRPIncentives.SchemeI.proposition_1_hrrp_i_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:21:29.020398+00:00
-- url     : https://prove2.me/theorems/be52c346-be49-4559-9a5d-83106bb24ddb
-- title:
--   Proposition 1 (Equilibrium under HRRP-I)
-- statement:
--   Throughout, $\lambda>0$ is the patients' arrival rate, the action box is $B=[r_{\min},r_{\max}]\times[c_{\min},c_{\max}]$, and the investment cost $R:B\to\mathbb R$ satisfies the standing assumptions of the paper (p. 10): $0<r_{\min}<r_{\max}<1$, $0\le c_{\min}<c_{\max}$, $R$ is non-increasing in each argument, jointly convex and twice differentiable on $B$, $R_{rr}R_{cc}>(R_{rc}+\lambda)^2$ and $R_{cr}\ge 0$ on $B$.
--
--   Let $N\ge2$ hospitals be paid by the HRRP-I transfer (9),
--
--   $$T_i=\bar c_i\lambda(1+r_i)-\frac{1}{\bar r_i}(r_i-\bar r_i)(1+r_i)\bar c_i\lambda+\bar R_i,$$
--
--   with yardsticks $\bar c_i,\bar r_i,\bar R_i$ the averages over the other $N-1$ hospitals (6), and let each hospital maximize $\Pi_i=T_i-c_i(1+r_i)\lambda-R(r_i,c_i)$ over its own pair $(r_i,c_i)\in B$. Then:
--
--   1. there exists at least one symmetric pure-strategy Nash equilibrium $(\tilde r,\tilde c)$;
--   2. every symmetric equilibrium satisfies
--   $$\tilde r<r^*,\qquad \tilde c>c^*,$$
--   where $(r^*,c^*)$ is the first best, the maximizer of social welfare $S(r,c)=V(\lambda)-c(1+r)\lambda-R(r,c)$ over $B$, lying in the open box $(r_{\min},r_{\max})\times(c_{\min},c_{\max})$;
--   3. if $N=2$, there is no asymmetric equilibrium: in every equilibrium both hospitals choose the same pair.
--
--   The result isolates the effect of the multiplier $(1+r_i)/\bar r_i$ in the readmission penalty: even with no cap and with bonuses, yardstick competition on readmissions drives hospitals to over-invest in readmission reduction and under-invest in cost reduction.
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
--   - encoding: there cannot be any asymmetric equilibrium → every equilibrium has equal actions for all hospitals; reason: the same statement, with asymmetric meaning that two hospitals choose different pairs
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, Proposition 1, p. 14

import Mathlib
import Definitions.Def_HRRPIncentives_SchemeI_Standing
import Definitions.Def_HRRPIncentives_SchemeI_welfare
import Definitions.Def_HRRPIncentives_SchemeI_IsEquilibrium

namespace HRRPIncentives.SchemeI

/-- Proposition 1 (Equilibrium under HRRP-I). Under the standing assumptions and the HRRP-I
transfer (9), for every number `N ≥ 2` of hospitals:
(a) there is at least one symmetric equilibrium `(r̃, c̃)`;
(b) every symmetric equilibrium satisfies `r̃ < r*` and `c̃ > c*`, where `(r*, c*)` is the
first-best maximizer of social welfare (2) on the box (interior, as in Lemma 1);
(c) if `N = 2`, every equilibrium is symmetric (there is no asymmetric equilibrium).

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, Proposition 1, p. 14.

**Formalization Note.** Equilibria are pure-strategy Nash equilibria with joint deviations over
the whole box (`IsEquilibrium`), not solutions of first-order conditions, and no interiority
of the equilibrium is assumed. Appendix A's boundary conditions, which are not in the artifact,
are dropped; clause (b) assumes instead the interiority of the first best that Lemma 1 derives
from them. "Decreasing" is read as antitone; `0 < λ`; `rmin < rmax` (see `Standing`). -/
theorem proposition_1_hrrp_i_equilibrium {lam rmin rmax cmin cmax : ℝ} (V : ℝ)
    {R : ℝ × ℝ → ℝ} (hR : Standing lam rmin rmax cmin cmax R) {N : ℕ} (hN : 2 ≤ N) :
    (∃ p ∈ box rmin rmax cmin cmax,
        IsEquilibrium lam rmin rmax cmin cmax R (fun _ : Fin N => p)) ∧
    (∀ p q : ℝ × ℝ, IsEquilibrium lam rmin rmax cmin cmax R (fun _ : Fin N => p) →
        q ∈ box rmin rmax cmin cmax →
        IsMaxOn (welfare lam V R) (box rmin rmax cmin cmax) q →
        rmin < q.1 → q.1 < rmax → cmin < q.2 → q.2 < cmax →
        p.1 < q.1 ∧ q.2 < p.2) ∧
    (N = 2 → ∀ x : Fin N → ℝ × ℝ, IsEquilibrium lam rmin rmax cmin cmax R x →
        ∀ i j, x i = x j) := by sorry

end HRRPIncentives.SchemeI
