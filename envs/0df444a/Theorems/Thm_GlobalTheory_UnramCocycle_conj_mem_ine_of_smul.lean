-- Prove2me | Theorems.Thm_GlobalTheory_UnramCocycle_conj_mem_ine_of_smul
-- name    : GlobalTheory.UnramCocycle.conj_mem_ine_of_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:15.704829+00:00
-- url     : https://prove2.me/theorems/39251568-4836-49e6-aa51-1cbb3e637dd0
-- title:
--   Unram Cocycle: conj mem ine of smul
-- statement:
--   The Unram Cocycle construction uses the conj mem ine of smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleUnramifiedOutsideVanishOnKernel.lean#L11-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleUnramifiedOutsideVanishOnKernel.lean#L11-L39

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleUnramifiedOutsideVanishOnKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open Pointwise
open GlobalTheory GlobalTheory.UnramCocycle

theorem GlobalTheory.UnramCocycle.conj_mem_ine_of_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (g σ : G F Ω) (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by sorry
