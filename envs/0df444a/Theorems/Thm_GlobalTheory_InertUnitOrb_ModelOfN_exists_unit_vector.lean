-- Prove2me | Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_exists_unit_vector
-- name    : GlobalTheory.InertUnitOrb.ModelOfN.exists_unit_vector
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:15:50.828168+00:00
-- url     : https://prove2.me/theorems/8f3f1ae0-4361-49b7-b2fb-f1c531e80e7e
-- title:
--   Model Of N: exists unit vector
-- statement:
--   The Model Of N construction uses the exists unit vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZero.lean#L69-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZero.lean#L69-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb GlobalTheory.InertUnitOrb.ModelOfN
variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]

theorem GlobalTheory.InertUnitOrb.ModelOfN.exists_unit_vector [FiniteDimensional K.E V] (h : V → V → K.E)
    (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z)
    (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z) (hsym : ∀ y z, h z y = K.c (h y z))
    (hpos : 0 < Module.finrank K.E V) (L : Submodule K.O V) (hfg : L.FG)
    (hspan : Submodule.span K.E (L : Set V) = ⊤)
    (hdual : ∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) :
    ∃ u ∈ L, h u u = 1 := by sorry
