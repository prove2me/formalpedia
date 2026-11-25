-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Glue_nondeg_of_pd
-- name    : GlobalTheory.Mass.Glue.nondeg_of_pd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:56.700476+00:00
-- url     : https://prove2.me/theorems/19b846cc-2de5-41c8-a268-ed0dde3dc40e
-- title:
--   Glue: nondeg of pd
-- statement:
--   The Glue construction uses the nondeg of pd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianLatticesGluedSubspaceComplement.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianLatticesGluedSubspaceComplement.lean#L22-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedSubspaceComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Glue
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.Mass.Glue.nondeg_of_pd [NumberField K] (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by sorry
