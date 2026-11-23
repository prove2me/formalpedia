-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticEtale_isIntegral_of_involution
-- name    : GlobalTheory.QuadraticEtale.isIntegral_of_involution
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:12.080638+00:00
-- url     : https://prove2.me/theorems/51839226-9d67-47fa-beb3-557956b0e26d
-- title:
--   Quadratic Etale: is Integral of involution
-- statement:
--   The Quadratic Etale construction uses the is Integral of involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L11-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsUnitFormSelfOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.QuadraticEtale
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →+* S)

theorem GlobalTheory.QuadraticEtale.isIntegral_of_involution (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap R S).range) : Algebra.IsIntegral R S := by sorry
