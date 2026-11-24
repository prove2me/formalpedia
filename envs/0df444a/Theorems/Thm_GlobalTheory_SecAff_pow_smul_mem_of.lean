-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_pow_smul_mem_of
-- name    : GlobalTheory.SecAff.pow_smul_mem_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:48:24.838167+00:00
-- url     : https://prove2.me/theorems/cb85073d-3d0f-4ab6-aa79-2c6f6c9cb6e9
-- title:
--   Sec Aff: pow smul mem of
-- statement:
--   The Sec Aff construction uses the pow smul mem of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L288-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L288-L316

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff

theorem GlobalTheory.SecAff.pow_smul_mem_of {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R' M'] {σ : R →+* R'} (F : M →ₛₗ[σ] M') (r : R)
    (h₁ : ∀ c : R', ∃ (n : ℕ) (d : R), σ d = σ r ^ n * c)
    (h₂ : ∀ s : M, F s = 0 → ∃ n : ℕ, r ^ n • s = 0) (W : Submodule R M) (s : M)
    (hs : F s ∈ Submodule.span R' (F '' W)) : ∃ N : ℕ, r ^ N • s ∈ W := by sorry
