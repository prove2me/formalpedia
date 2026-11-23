-- Prove2me | Theorems.Thm_GlobalTheory_NormCompat_locUnit_apply
-- name    : GlobalTheory.NormCompat.locUnit_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:04.650303+00:00
-- url     : https://prove2.me/theorems/c1f3c3f9-1e5b-44ad-8ad0-8270e4ef59a2
-- title:
--   Norm Compat: loc Unit apply
-- statement:
--   The Norm Compat construction uses the loc Unit apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocUnitApply.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocUnitApply.lean#L13-L14

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory GlobalTheory.NormCompat

theorem GlobalTheory.NormCompat.locUnit_apply (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    locUnit F v a = localIdele F v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) := by sorry
