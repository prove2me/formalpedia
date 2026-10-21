-- Prove2me | Theorems.Thm_InvShareComp_Exog_proposition_1c
-- name    : InvShareComp.Exog.proposition_1c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:06.331866+00:00
-- url     : https://prove2.me/theorems/fc4b5399-094a-4da8-abf4-44c8631c850b
-- title:
--   Proposition 1(c), second clause, p. 15 (PDF 15), corrected — for t ≥ (c̄ − δ)/2 with ŝ(t, I) ≥ 0, sharing is weakly better
-- statement:
--   Under the standing assumptions, with exchangeable demand factors on $[0,1]^2$ having a density, $I\in[0,1]$ and a transfer price
--   $$\frac{\bar c-\delta}{2}\le t\le\bar c-\delta$$
--   at which the closed-form sharing service level is non-negative ($p\mu-A-B\ge0$), the profit difference
--   $$\hat\Delta(t,I)=\hat\pi_i(t,I)-\hat\pi^N_i(I)\ \ge\ 0 .$$
--
--   At a high enough transfer price each retailer is at least as well off sharing inventory as not sharing; this is the comparison Proposition 2 uses at $t=\bar c-\delta$.
--
--   **Formalization Note.** *Corrected.* The hypothesis $\hat s(t,I)\ge0$ is added: the proof bounds $-k(\hat s^2-(\hat s^N)^2)$ using $0\le\hat s\le\hat s^N$, and the paper's claim "$\hat s(t,I)>0$" is unproved and false for the bimodal instance recorded at Lemma 3(c). Only the clause "when $t\ge\frac{\bar c-\delta}2$, $\hat\Delta(t,I)\ge0$" is formalized; the monotonicity claims in $t$ and $\beta$ are not.
-- source:
--   Guo & Jiang, Inventory Sharing under Service Competition, SSRN 3512712 (version of March 2, 2023; forthcoming at MSOM), p. 15 (PDF 15), Proposition 1(c); proof in Online Appendix p. 9 (PDF 41)

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

namespace InvShareComp.Exog

open MeasureTheory Classical

theorem proposition_1c (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ))
    (hν : IsDemandLaw ν) (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc ((P.cbar - P.δ) / 2) (P.cbar - P.δ))
    (hS : 0 ≤ SVal P ν t I) :
    piHatN P ν I ≤ piHat P ν t I := by sorry

end InvShareComp.Exog
