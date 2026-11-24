-- Prove2me | Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff
-- name    : GlobalTheory.HermLat.mem_perp_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:50:15.765088+00:00
-- url     : https://prove2.me/theorems/d6a1c30e-c7f9-4776-9eae-ee0e56058e0c
-- title:
--   Herm Lat: mem perp iff
-- statement:
--   The Herm Lat construction uses the mem perp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/FlagPairDefinitePartLattice.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/FlagPairDefinitePartLattice.lean#L31-L33

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

theorem GlobalTheory.HermLat.mem_perp_iff (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (S : Submodule K V) (y : V) :
    y ∈ _root_.GlobalTheory.HermLat.perp H S ↔ ∀ x ∈ S, H.B y x = 0 := by sorry
