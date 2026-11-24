-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_comp_mulVec_ev
-- name    : GlobalTheory.JR.HermInv.comp_mulVec_ev
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:33:49.88394+00:00
-- url     : https://prove2.me/theorems/f7fc730c-38fd-4228-884f-53a8e06646da
-- title:
--   Herm Inv: comp mul Vec ev
-- statement:
--   The Herm Inv construction uses the comp mul Vec ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L97-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L97-L105

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
variable {r : ℕ} {K : Type} [CommRing K]

theorem GlobalTheory.JR.HermInv.comp_mulVec_ev (p : Fin r → K) (j : ℕ) (hj : j + 1 < r) : companion p *ᵥ ev r K j = ev r K (j + 1) := by sorry
