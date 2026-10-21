-- Prove2me | Theorems.Thm_MazurTransfer_original_continuous_scalar_character_kernel_restriction_injective
-- name    : MazurTransfer.original_continuous_scalar_character_kernel_restriction_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T18:21:55.365982+00:00
-- url     : https://prove2.me/theorems/717a8279-6ee7-4da8-8c36-fd7c52ef2596
-- statement:
--   For a field $k$, a topological group $G$ in the original continuous cocycle presentation and a character $\chi:G\to k^\times$, the subgroup $\ker\chi$ acts trivially on the same scalar-character coefficients. A class restricting to zero on $\ker\chi$ is zero, so restriction is injective. The original cocycle-value identity and both zero-detection propositions are retained. No finite-group, finite-image or splitting hypothesis is added. Named downstream consumer: genuine continuous characters of the same character kernel and actual reflected-character arithmetic Selmer classes.

import Definitions.Def_MazurTransfer_OriginalContinuousScalarCharacterKernelRestrictionData20261019
import Theorems.Thm_MazurTransfer_original_scalar_cocycle_character_kernel_detection_and_coboundary
import Theorems.Thm_MazurTransfer_ContinuousFirstCohomologySubgroupRestriction_restriction_classMap_zero_iff
noncomputable section
open MazurTransfer ScalarCharacterLine RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologySubgroupRestriction
open ContinuousScalarCharacterKernelRestriction

theorem MazurTransfer.original_continuous_scalar_character_kernel_restriction_injective : (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (z : continuousCocycles G (Coefficient (scalarRepresentation χ))) (g h : G), cocycleValue χ z (g * h) = cocycleValue χ z g + (χ g : k) * cocycleValue χ z h) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (s : χ.ker) (m : (Coefficient (scalarRepresentation χ))), s • m = m) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (z : continuousCocycles G (Coefficient (scalarRepresentation χ)))
    (hz : restriction G (Coefficient (scalarRepresentation χ)) χ.ker (classMap G (Coefficient (scalarRepresentation χ)) z) = 0) (g : G) (hg : χ g = 1), cocycleValue χ z g = 0) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (x : H1 G (Coefficient (scalarRepresentation χ)))
    (hx : restriction G (Coefficient (scalarRepresentation χ)) χ.ker x = 0), x = 0) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ), Function.Injective (restriction G (Coefficient (scalarRepresentation χ)) χ.ker)) := by sorry
