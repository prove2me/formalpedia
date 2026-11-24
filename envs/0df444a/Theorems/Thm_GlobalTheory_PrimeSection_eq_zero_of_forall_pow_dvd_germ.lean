-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_eq_zero_of_forall_pow_dvd_germ
-- name    : GlobalTheory.PrimeSection.eq_zero_of_forall_pow_dvd_germ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:28:35.259172+00:00
-- url     : https://prove2.me/theorems/76daa560-546b-4d50-a74a-70383ca39a98
-- title:
--   Prime Section: eq zero of forall pow dvd germ
-- statement:
--   The Prime Section construction uses the eq zero of forall pow dvd germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L78-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L78-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} [IsIntegral X]

theorem GlobalTheory.PrimeSection.eq_zero_of_forall_pow_dvd_germ [IsLocallyNoetherian X] {t : Γ(X, ⊤)}
    {ι : Type v} {U : ι → X.Opens} (g : ∀ a b, Γ(X, U a ⊓ U b)) (s : ∀ a, Γ(X, U a))
    (hs : ∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b))
    {a : ι} {x : X} (hx : x ∈ U a) (hxt : x ∉ X.basicOpen t)
    (h : ∀ e : ℕ, X.presheaf.germ ⊤ x trivial t ^ e ∣ X.presheaf.germ (U a) x hx (s a))
    (b : ι) : s b = 0 := by sorry
