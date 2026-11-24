-- Prove2me | Theorems.Thm_GlobalTheory_HermLat_isUnimod_iff
-- name    : GlobalTheory.HermLat.isUnimod_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:29.456908+00:00
-- url     : https://prove2.me/theorems/351e988a-ebfc-4ecb-aa4e-02242002348a
-- title:
--   Herm Lat: is Unimod iff
-- statement:
--   The Herm Lat construction uses the is Unimod iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/FlagPairDefinitePartLattice.lean#L86-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/FlagPairDefinitePartLattice.lean#L86-L99

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_AutFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.HermitianLatticeCounting.S6
open GlobalTheory GlobalTheory.HermLat
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]

theorem GlobalTheory.HermLat.isUnimod_iff (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (M : Submodule R V) :
    _root_.GlobalTheory.HermLat.IsUnimod H M ↔ Submodule.IsLattice K M ∧ _root_.Formalism.HermitianLatticesTheory.IsUnimodular H.B.flip M := by sorry
