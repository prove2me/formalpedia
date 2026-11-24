-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_part3
-- name    : GlobalTheory.JR.HermInv.part3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:33:39.204425+00:00
-- url     : https://prove2.me/theorems/c40c3ed2-5cc9-4ba2-b6bb-fe1d282545fc
-- title:
--   Herm Inv: part3
-- statement:
--   The Herm Inv construction uses the part3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L330-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L330-L370

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

theorem GlobalTheory.JR.HermInv.part3 (X₁ X₂ : Hn r F E) (a : Inv r F) (hΔ : Delta a ≠ 0) (h₁ : HasInv X₁ a) (h₂ : HasInv X₂ a) :
    ∃! g : Matrix.unitaryGroup (Fin r) E, actU g X₁ = X₂ := by sorry
