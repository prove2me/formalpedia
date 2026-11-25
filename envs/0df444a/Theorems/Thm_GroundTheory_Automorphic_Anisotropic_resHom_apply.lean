-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_resHom_apply
-- name    : GroundTheory.Automorphic.Anisotropic.resHom_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:22:31.24309+00:00
-- url     : https://prove2.me/theorems/494ac968-bb64-43b3-8245-c03c7b3fcb79
-- title:
--   Anisotropic: res Hom apply
-- statement:
--   The Anisotropic construction uses the res Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L26-L27

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicUnitaryRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Module Matrix TensorProduct
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Anisotropic
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
local notation "𝒩" => Fintype.card (ι × κ)

theorem GroundTheory.Automorphic.Anisotropic.resHom_apply (M : Matrix ι ι (R ⊗[K] E)) (p q : Fin 𝒩) :
    resHom b R M p q = blockHom b R M ((Fintype.equivFin (ι × κ)).symm p) ((Fintype.equivFin (ι × κ)).symm q) := by sorry
