-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_form_pow
-- name    : GlobalTheory.JR.HermInv.form_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:01.609798+00:00
-- url     : https://prove2.me/theorems/093846ad-fce6-4175-83da-d83b10d07b18
-- title:
--   Herm Inv: form pow
-- statement:
--   The Herm Inv construction uses the form pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L171-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L171-L173

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}

theorem GlobalTheory.JR.HermInv.form_pow (A : Matrix (Fin r) (Fin r) E) (hA : IsSelfAdjoint A) (v w : Fin r → E) (k : ℕ) :
    star (A ^ k *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ (A ^ k *ᵥ w) := by sorry
