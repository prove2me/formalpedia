-- Prove2me | Theorems.Thm_GlobalTheory_UnramCocycle_kerSub_normal
-- name    : GlobalTheory.UnramCocycle.kerSub_normal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:18.163178+00:00
-- url     : https://prove2.me/theorems/9c697655-6a13-4913-8ebd-10899e7a62c9
-- title:
--   Unram Cocycle: ker Sub normal
-- statement:
--   The Unram Cocycle construction uses the ker Sub normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleUnramifiedOutsideVanishOnKernel.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleUnramifiedOutsideVanishOnKernel.lean#L60-L72

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

theorem GlobalTheory.UnramCocycle.kerSub_normal {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M)
    (x : Z1 ρ) : (kerSub ρ x).Normal := by sorry
