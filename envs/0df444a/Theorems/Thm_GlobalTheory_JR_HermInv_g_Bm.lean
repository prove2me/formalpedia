-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_g_Bm
-- name    : GlobalTheory.JR.HermInv.g_Bm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:33:44.725796+00:00
-- url     : https://prove2.me/theorems/5d0cc0c5-367c-43ec-a744-442c15c1f581
-- title:
--   Herm Inv: g Bm
-- statement:
--   The Herm Inv construction uses the g Bm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L318-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L318-L328

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

theorem GlobalTheory.JR.HermInv.g_Bm (g : Matrix.unitaryGroup (Fin r) E) (X₁ X₂ : Hn r F E) (hact : actU g X₁ = X₂) :
    g.1 * Bm X₁.toGl = Bm X₂.toGl := by sorry
