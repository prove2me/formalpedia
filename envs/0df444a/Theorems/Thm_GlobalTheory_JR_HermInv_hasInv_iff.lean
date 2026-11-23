-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_hasInv_iff
-- name    : GlobalTheory.JR.HermInv.hasInv_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:26.124485+00:00
-- url     : https://prove2.me/theorems/4dbd783c-081a-4baa-8e81-374851251b04
-- title:
--   Herm Inv: has Inv iff
-- statement:
--   The Herm Inv construction uses the has Inv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L152-L156

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

theorem GlobalTheory.JR.HermInv.hasInv_iff (X : Hn r F E) (a : Inv r F) : HasInv X a ↔
    (∀ i : Fin r, X.1.1.charpoly.coeff i = algebraMap F E (a.1 i)) ∧
    (∀ i : Fin r, mom X.toGl i = algebraMap F E (a.2.1 i)) ∧ X.2.2 = a.2.2 := by sorry
