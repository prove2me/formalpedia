-- Prove2me | Theorems.Thm_GlobalTheory_HermLat_mem_isomGrp
-- name    : GlobalTheory.HermLat.mem_isomGrp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:49:32.598474+00:00
-- url     : https://prove2.me/theorems/d90f500c-e17d-402a-8517-0d79fae3d7c4
-- title:
--   Herm Lat: mem isom Grp
-- statement:
--   The Herm Lat construction uses the mem isom Grp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/FlagPairDefinitePartLattice.lean#L187-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/FlagPairDefinitePartLattice.lean#L187-L192

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

theorem GlobalTheory.HermLat.mem_isomGrp (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (s : V ≃ₗ[K] V) :
    s ∈ _root_.GlobalTheory.HermLat.isomGrp H ↔ ∀ x y, H.B (s x) (s y) = H.B x y := by sorry
