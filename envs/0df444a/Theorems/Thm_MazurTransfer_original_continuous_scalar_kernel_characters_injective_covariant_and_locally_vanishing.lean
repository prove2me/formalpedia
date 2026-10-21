-- Prove2me | Theorems.Thm_MazurTransfer_original_continuous_scalar_kernel_characters_injective_covariant_and_locally_vanishing
-- name    : MazurTransfer.original_continuous_scalar_kernel_characters_injective_covariant_and_locally_vanishing
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T18:39:17.204241+00:00
-- url     : https://prove2.me/theorems/9b99924d-96d0-4005-a34e-89c113d74a35
-- statement:
--   For the same field, group, topology and scalar character $χ$, the original map from continuous $H^1$ to genuine continuous characters of $\ker χ$ is injective. Its cocycle formula gives conjugation covariance with scalar $χ(g)$. If a class restricts to zero on a supplied subgroup, its character vanishes on the intersection with that subgroup. All six complete original propositions and every original local subgroup hypothesis are retained. Named downstream consumer: the fixed arithmetic unramified character-kernel embedding.

import Definitions.Def_MazurTransfer_OriginalContinuousScalarKernelCharacterMapsData20261019
import Theorems.Thm_MazurTransfer_original_continuous_scalar_character_kernel_restriction_injective
import Theorems.Thm_MazurTransfer_original_trivial_continuous_cohomology_characters_bijective
noncomputable section
open MazurTransfer ScalarCharacterLine RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologySubgroupRestriction
open ContinuousScalarCharacterKernelRestriction ContinuousScalarKernelCharacters

theorem MazurTransfer.original_continuous_scalar_kernel_characters_injective_covariant_and_locally_vanishing : (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ), Function.Injective (kernelCharacters χ)) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (z : continuousCocycles G (Coefficient (scalarRepresentation χ))) (s : χ.ker), ((kernelCharacters χ (classMap G (Coefficient (scalarRepresentation χ)) z)).toMul s).val = cocycleValue χ z s.val) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (z : continuousCocycles G (Coefficient (scalarRepresentation χ))), cocycleValue χ z 1 = 0) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (z : continuousCocycles G (Coefficient (scalarRepresentation χ))) (g : G) (s : χ.ker), cocycleValue χ z (g * s.val * g⁻¹) = (χ g : k) * cocycleValue χ z s.val) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (x : H1 G (Coefficient (scalarRepresentation χ))) (g : G) (s : χ.ker), ((kernelCharacters χ x).toMul (conjugateKernelElement χ g s)).val =
      (χ g : k) * ((kernelCharacters χ x).toMul s).val) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (x : H1 G (Coefficient (scalarRepresentation χ))) (T : Subgroup G)
    (hx : restriction G (Coefficient (scalarRepresentation χ)) T x = 0) (s : χ.ker) (hs : s.val ∈ T), (kernelCharacters χ x).toMul s = 1) := by sorry
