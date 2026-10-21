-- Prove2me | Theorems.Thm_InvShareComp_Exog_closed_form_profits
-- name    : InvShareComp.Exog.closed_form_profits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:15.414022+00:00
-- url     : https://prove2.me/theorems/7c17bef8-9a23-461a-9449-0909c596dbe7
-- title:
--   (A.9) and (A.11), Online Appendix pp. 6, 8 (PDF 38, 40) — closed-form profits at the stated service levels
-- statement:
--   Under the standing assumptions, with exchangeable demand factors on $[0,1]^2$ having a density, $I\in[0,1]$ and $t\in[0,\bar c-\delta]$, the profits at the paper's closed-form service levels (where $d_1=d_2=\tfrac12$) are
--
--   1. without sharing,
--   $$\hat\pi^N_i(I)=E\Bigl[p\,\tfrac{\varepsilon_1}{2}-\bar c\bigl(\tfrac{\varepsilon_1}{2}-I\bigr)^+\Bigr]-k\hat s^N(I)^2-cI,$$
--   2. with sharing at $t$,
--   $$\hat\pi_i(t,I)=E\Bigl[p\,\tfrac{\varepsilon_1}{2}-\delta\bigl(\min\{\tfrac{\varepsilon_1}{2}-I,\,I-\tfrac{\varepsilon_2}{2}\}\bigr)^+-\bar c\bigl((\tfrac{\varepsilon_1}{2}-I)^+-(I-\tfrac{\varepsilon_2}{2})^+\bigr)^+\Bigr]-k\hat s(t,I)^2-cI .$$
--
--   These are (A.9) and (A.11). The operational part of the sharing profit is independent of $t$; its service-cost term depends on $t$ through $\hat s(t,I)$.
--
--   **Formalization Note.** The second form is a compact rewriting of (A.11): splitting the expectation over the regions of Lemma 3(a) gives the paper's iterated integrals. The paper prints $\hat s^2(I)$ in (A.11); its surrounding equations identify this as $\hat s(t,I)^2$.
-- source:
--   Guo & Jiang, Inventory Sharing under Service Competition, SSRN 3512712 (version of March 2, 2023; forthcoming at MSOM), Online Appendix p. 6 (PDF 38), equation (A.9), and p. 8 (PDF 40), equation (A.11)

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

namespace InvShareComp.Exog

open MeasureTheory Classical

theorem closed_form_profits (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ))
    (hν : IsDemandLaw ν) (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc 0 (P.cbar - P.δ)) :
    profitNo1 P ν I I (sHatN P ν I) (sHatN P ν I)
        = (∫ ω, (P.p * (ω.1 / 2) - P.cbar * max (ω.1 / 2 - I) 0) ∂ν)
          - P.k * (sHatN P ν I) ^ 2 - P.c * I ∧
    profitShare1 P ν t I I (sHat P ν t I) (sHat P ν t I)
        = (∫ ω, (P.p * (ω.1 / 2) - P.δ * max (min (ω.1 / 2 - I) (I - ω.2 / 2)) 0
            - P.cbar * max (max (ω.1 / 2 - I) 0 - max (I - ω.2 / 2) 0) 0) ∂ν)
          - P.k * (sHat P ν t I) ^ 2 - P.c * I := by sorry

end InvShareComp.Exog
