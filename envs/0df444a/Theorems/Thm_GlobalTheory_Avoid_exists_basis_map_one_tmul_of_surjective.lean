-- Prove2me | Theorems.Thm_GlobalTheory_Avoid_exists_basis_map_one_tmul_of_surjective
-- name    : GlobalTheory.Avoid.exists_basis_map_one_tmul_of_surjective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:57:12.925478+00:00
-- url     : https://prove2.me/theorems/bc319f2b-0c27-4641-ae33-f4375a7d25ca
-- title:
--   Avoid: exists basis map one tmul of surjective
-- statement:
--   The Avoid construction uses the exists basis map one tmul of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisMapOfLiftBaseChangeSurjective.lean#L19-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisMapOfLiftBaseChangeSurjective.lean#L19-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisMapOfLiftBaseChangeSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open scoped TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.Avoid
open Module Function
open scoped TensorProduct Pointwise

theorem GlobalTheory.Avoid.exists_basis_map_one_tmul_of_surjective {K L V W ι : Type*} [CommRing K] [Field L]
    [Algebra K L] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
    [Module.Finite L W] {d : ℕ} (hd : finrank L W = d) (G : L ⊗[K] V →ₗ[L] W)
    (hG : Surjective G) (v : ι → V) (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ (σ : Fin d → ι) (b : Basis (Fin d) L W), Injective σ ∧ ∀ k, b k = G (1 ⊗ₜ v (σ k)) := by sorry
