-- Prove2me | Theorems.Thm_InvShareComp_Exog_lemma_3c_t
-- name    : InvShareComp.Exog.lemma_3c_t
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:16.82932+00:00
-- url     : https://prove2.me/theorems/fc804bd3-3bb9-4c93-af7c-2bdb40c928d2
-- title:
--   Lemma 3(c), t-part, p. 13 (PDF 13), corrected — π̂ᵢ(t, I) is non-decreasing in t when ŝ(c̄ − δ, I) ≥ 0
-- statement:
--   Under the standing assumptions, with exchangeable demand factors on $[0,1]^2$ having a density and $I\in[0,1]$, suppose
--   $$p\mu-A-B\ \ge\ 0\quad\text{at } t=\bar c-\delta,$$
--   i.e. the closed-form service level $\hat s(\bar c-\delta,I)$ is non-negative. Then retailer $i$'s profit at the closed-form level,
--   $$t\longmapsto\hat\pi_i(t,I)=\pi_i\bigl(\hat s(t,I),I\mid\hat s(t,I),I\bigr),$$
--   is non-decreasing on $[0,\bar c-\delta]$.
--
--   This is the step of Proposition 2's proof that singles out the largest non-moot transfer price.
--
--   **Formalization Note.** *Corrected.* The paper's argument $\partial\hat\pi_i/\partial t=-2k\hat s\,\partial\hat s/\partial t>0$ needs $\hat s\ge 0$, which the paper does not establish. Without the hypothesis the statement fails: for i.i.d. bimodal demand (density $\propto e^{-(x-0.05)^2/0.002}+e^{-(x-0.95)^2/0.002}$ on $[0,1]$) with $p=1$, $\bar c=0.9$, $\delta=0$, $c=0.3$, $I=0.324$, $\beta=0.1$, $k=1$, the profit peaks near $t\approx0.605$ and falls afterwards. Monotonicity is weak (no strictness when no sharing occurs, e.g. $I=0$). The other parts of Lemma 3(c) are not formalized.
-- source:
--   Guo & Jiang, Inventory Sharing under Service Competition, SSRN 3512712 (version of March 2, 2023; forthcoming at MSOM), p. 13 (PDF 13), Lemma 3(c); proof in Online Appendix p. 8 (PDF 40)

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

namespace InvShareComp.Exog

open MeasureTheory Classical

theorem lemma_3c_t (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ)) (hν : IsDemandLaw ν)
    (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (hS0 : 0 ≤ SVal P ν (P.cbar - P.δ) I) :
    MonotoneOn (fun t => piHat P ν t I) (Set.Icc 0 (P.cbar - P.δ)) := by sorry

end InvShareComp.Exog
