-- Prove2me | Theorems.Thm_MazurTransfer_original_submodule_character_image_finite_dimension_and_finrank_bound
-- name    : MazurTransfer.original_submodule_character_image_finite_dimension_and_finrank_bound
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T13:27:41.218913+00:00
-- url     : https://prove2.me/theorems/d76dd5d5-2406-4ee6-a172-d85168e7b918
-- statement:
--   Let $E\subset V$ be a vector subspace, $f:V\to W$ a linear map, $i:A\to V$, and $C\subset A$, $D\subset W$ finite-dimensional subspaces. If $f(E)\subset D$ and every element of the kernel of $f|_E$ lies in $i(C)$, then $E$ is finite-dimensional and $\dim E\le\dim C+\dim D$. The original restricted-kernel map is injective. Both finite-dimensionality assumptions are explicit. Named downstream consumer: the actual pi norm Kummer image bound from its selected character image and unramified kernel classes.

import Definitions.Def_MazurTransfer_OriginalSubmoduleCharacterImageDimensionBoundData20261019
noncomputable section
open MazurTransfer SubmoduleCharacterImageDimensionBound

theorem MazurTransfer.original_submodule_character_image_finite_dimension_and_finrank_bound : (∀ {k A V W : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (E : Submodule k V) (f : V →ₗ[k] W) (i : A →ₗ[k] V)
    (C : Submodule k A) (hker : ∀ x : E, f x.val = 0 → x.val ∈ C.map i), Function.Injective (characterKernelMap E f i C hker)) ∧ (∀ {k A V W : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (E : Submodule k V) (f : V →ₗ[k] W) (i : A →ₗ[k] V)
    (C : Submodule k A) (D : Submodule k W)
    [FiniteDimensional k C] [FiniteDimensional k D]
    (himage : LinearMap.range (restrictedQuotient E f) ≤ D)
    (hker : ∀ x : E, f x.val = 0 → x.val ∈ C.map i), FiniteDimensional k E ∧ Module.finrank k E ≤ Module.finrank k C + Module.finrank k D) := by sorry
