-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_absSpace_one_eq_top_of_norm_charpoly_roots
-- name    : GlobalTheory.WeilDeligne.absSpace_one_eq_top_of_norm_charpoly_roots
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:08:31.107893+00:00
-- url     : https://prove2.me/theorems/ae9d6eed-3cf7-43df-b74a-b2e37bd45e2f
-- title:
--   Weil Deligne: abs Space one eq top of norm charpoly roots
-- statement:
--   The Weil Deligne construction uses the abs Space one eq top of norm charpoly roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/TemperedOfLpDimLeOneOfUnitEigenvalues.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/TemperedOfLpDimLeOneOfUnitEigenvalues.lean#L19-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_TemperedOfLpDimLeOneOfUnitEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne

theorem GlobalTheory.WeilDeligne.absSpace_one_eq_top_of_norm_charpoly_roots {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hs : f.IsSemisimple) (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) :
    absSpace f 1 = ⊤ := by sorry
