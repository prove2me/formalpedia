-- Prove2me | Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_herm_add_right
-- name    : GlobalTheory.InertUnitOrb.ModelOfN.herm_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:13.026267+00:00
-- url     : https://prove2.me/theorems/54f3dd4e-8c0b-415d-83fc-2f03c82f61d0
-- title:
--   Model Of N: herm add right
-- statement:
--   The Model Of N construction uses the herm add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZero.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZero.lean#L57-L59

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

theorem GlobalTheory.InertUnitOrb.ModelOfN.herm_add_right (h : V → V → K.E) (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z)
    (hsym : ∀ y z, h z y = K.c (h y z)) (y z z' : V) : h y (z + z') = h y z + h y z' := by sorry
