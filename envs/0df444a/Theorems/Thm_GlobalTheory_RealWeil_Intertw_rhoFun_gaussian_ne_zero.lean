-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Intertw_rhoFun_gaussian_ne_zero
-- name    : GlobalTheory.RealWeil.Intertw.rhoFun_gaussian_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:13.874027+00:00
-- url     : https://prove2.me/theorems/04214683-1ac5-42c0-bf76-6c57e3ba5027
-- title:
--   Intertw: rho Fun gaussian ne zero
-- statement:
--   The Intertw construction uses the rho Fun gaussian ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntertwiningSymplecticAndGroupLaw.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntertwiningSymplecticAndGroupLaw.lean#L39-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwiningSymplecticAndGroupLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Intertw
variable {l : Type} [Fintype l]

theorem GlobalTheory.RealWeil.Intertw.rhoFun_gaussian_ne_zero (w : l ⊕ l → ℝ) :
    rhoFun w ⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)) (-pPart w) ≠ 0 := by sorry
