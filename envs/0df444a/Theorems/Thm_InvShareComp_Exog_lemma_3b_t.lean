-- Prove2me | Theorems.Thm_InvShareComp_Exog_lemma_3b_t
-- name    : InvShareComp.Exog.lemma_3b_t
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:04.422579+00:00
-- url     : https://prove2.me/theorems/0e91f104-ba4f-4928-a118-8f67d367fc00
-- title:
--   Lemma 3(b), t-part, p. 13 (PDF 13) — ŝ(t, I) is non-increasing in t on [0, c̄ − δ]
-- statement:
--   Under the standing assumptions, with exchangeable demand factors on $[0,1]^2$ having a density and $I\in[0,1]$, the closed-form sharing service level
--   $$t\longmapsto \hat s(t,I)=\frac{\beta(p\mu-A-B)}{2k}$$
--   is non-increasing on the non-moot range $[0,\bar c-\delta]$.
--
--   A higher transfer price makes selling leftover inventory to the rival more attractive and so weakens the incentive to compete on service.
--
--   **Formalization Note.** The paper says "decreases in $t$"; the monotonicity is stated weakly because it is not strict when no sharing ever occurs (e.g. $I=0$, or $\beta=0$). The other parts of Lemma 3(b) (in $\beta$, $\delta$, $\bar c$, $I$) are not formalized.
-- source:
--   Guo & Jiang, Inventory Sharing under Service Competition, SSRN 3512712 (version of March 2, 2023; forthcoming at MSOM), p. 13 (PDF 13), Lemma 3(b); proof in Online Appendix p. 7 (PDF 39)

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

namespace InvShareComp.Exog

open MeasureTheory Classical

theorem lemma_3b_t (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ)) (hν : IsDemandLaw ν)
    (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1) :
    AntitoneOn (fun t => sHat P ν t I) (Set.Icc 0 (P.cbar - P.δ)) := by sorry

end InvShareComp.Exog
