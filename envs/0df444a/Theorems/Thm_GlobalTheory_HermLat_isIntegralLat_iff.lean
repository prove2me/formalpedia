-- Prove2me | Theorems.Thm_GlobalTheory_HermLat_isIntegralLat_iff
-- name    : GlobalTheory.HermLat.isIntegralLat_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:37.752871+00:00
-- url     : https://prove2.me/theorems/a680c36a-806e-4f55-ae91-7d239990e02e
-- title:
--   Herm Lat: is Integral Lat iff
-- statement:
--   The Herm Lat construction uses the is Integral Lat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/FlagPairDefinitePartLattice.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/FlagPairDefinitePartLattice.lean#L47-L51

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

theorem GlobalTheory.HermLat.isIntegralLat_iff (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V) (M : Submodule R V) :
    _root_.GlobalTheory.HermLat.IsIntegralLat H M ↔ ∀ x ∈ M, ∀ y ∈ M, H.B x y ∈ (1 : Submodule R K) := by sorry
