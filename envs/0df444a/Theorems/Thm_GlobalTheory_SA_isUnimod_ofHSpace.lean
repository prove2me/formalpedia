-- Prove2me | Theorems.Thm_GlobalTheory_SA_isUnimod_ofHSpace
-- name    : GlobalTheory.SA.isUnimod_ofHSpace
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:35:24.59054+00:00
-- url     : https://prove2.me/theorems/e774eb8f-bdb1-496c-b83f-0dedffb3a691
-- title:
--   SA: is Unimod of HSpace
-- statement:
--   The SA construction uses the is Unimod of HSpace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SymmetricFlagBasisVectorsApplyCentre.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SymmetricFlagBasisVectorsApplyCentre.lean#L20-L23

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SA
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat

theorem GlobalTheory.SA.isUnimod_ofHSpace {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (Λ : Submodule (NumberField.RingOfIntegers E) S.V) :
    IsUnimod (ofHSpace S) Λ ↔ Submodule.IsLattice E Λ ∧ Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ := by sorry
