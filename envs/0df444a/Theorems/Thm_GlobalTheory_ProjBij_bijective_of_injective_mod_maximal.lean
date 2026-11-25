-- Prove2me | Theorems.Thm_GlobalTheory_ProjBij_bijective_of_injective_mod_maximal
-- name    : GlobalTheory.ProjBij.bijective_of_injective_mod_maximal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:37.787595+00:00
-- url     : https://prove2.me/theorems/1a7961a8-c0ed-509e-b1de-a5f22543213a
-- title:
--   Proj Bij: bijective of injective mod maximal
-- statement:
--   The Proj Bij construction uses the bijective of injective mod maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfInjectiveModMaximal.lean#L30-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfInjectiveModMaximal.lean#L30-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfInjectiveModMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.ProjBij

theorem GlobalTheory.ProjBij.bijective_of_injective_mod_maximal
    (R M N : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N)
    (hrk : ∀ m : Ideal R, m.IsMaximal →
      Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N))
    (hinj : ∀ m : Ideal R, m.IsMaximal → ∀ x, f x ∈ m • (⊤ : Submodule R N) →
      x ∈ m • (⊤ : Submodule R M)) :
    Function.Bijective f := by sorry
