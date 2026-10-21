-- Prove2me | Theorems.Thm_InvShareComp_Exog_central_identity
-- name    : InvShareComp.Exog.central_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:12.1577+00:00
-- url     : https://prove2.me/theorems/f9c971d5-b066-41c8-aa6a-e353ceb66004
-- title:
--   Proof of Proposition 2, Online Appendix p. 10 (PDF 42) — π_i(s, I | s, I) = π^c(I, I)/2 − k s²
-- statement:
--   Under the standing assumptions, with exchangeable demand factors on $[0,1]^2$ having a density, $I\in[0,1]$ and $t\in[0,\bar c-\delta]$, for every service level $s$,
--   $$\pi_i(s,I\mid s,I)=\frac{\pi^c(I,I)}{2}-ks^2,$$
--   where $\pi^c$ is the centralized profit (A.1) at zero service.
--
--   So a symmetric sharing profile reproduces the centralized system's half-profit exactly, minus the service cost; it is the identity behind the paper's claim that coordination requires zero service.
--
--   **Formalization Note.** The identity uses exchangeability (Lemma A.1) to cancel the transfer payments and to split the pooled shortage cost evenly.
-- source:
--   Guo & Jiang, Inventory Sharing under Service Competition, SSRN 3512712 (version of March 2, 2023; forthcoming at MSOM), Online Appendix p. 10 (PDF 42), proof of Proposition 2; (A.1), Online Appendix p. 3 (PDF 35)

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

namespace InvShareComp.Exog

open MeasureTheory Classical

theorem central_identity (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ))
    (hν : IsDemandLaw ν) (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc 0 (P.cbar - P.δ)) (s : ℝ) :
    profitShare1 P ν t I I s s = centralProfit P ν I I / 2 - P.k * s ^ 2 := by sorry

end InvShareComp.Exog
