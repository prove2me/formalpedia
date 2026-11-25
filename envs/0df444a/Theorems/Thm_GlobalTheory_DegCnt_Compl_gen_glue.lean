-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_Compl_gen_glue
-- name    : GlobalTheory.DegCnt.Compl.gen_glue
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:17:20.923914+00:00
-- url     : https://prove2.me/theorems/8dd11dfe-1ae5-5ecc-a8d9-3e05e5b310dd
-- title:
--   Compl: gen glue
-- statement:
--   The Compl construction uses the gen glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IdxSupRight.lean#L36-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IdxSupRight.lean#L36-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IdxSupRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Compl
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

theorem GlobalTheory.DegCnt.Compl.gen_glue (M U U' : Submodule R W) (t : Finset W)
    (h : U ⊓ (M ⊔ U') = (M ⊓ U) ⊔ Submodule.span R (t : Set W)) :
    ∃ t' : Finset W, t'.card ≤ t.card ∧ U' ⊓ (M ⊔ U) = (M ⊓ U') ⊔ Submodule.span R (t' : Set W) := by sorry
