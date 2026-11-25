-- Prove2me | Theorems.Thm_GlobalTheory_FlatFibreRegular_eq_zero_of_mul_eq_zero
-- name    : GlobalTheory.FlatFibreRegular.eq_zero_of_mul_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:00.826115+00:00
-- url     : https://prove2.me/theorems/f498aa2e-9415-4bce-852e-c732fd724f54
-- title:
--   Flat Fibre Regular: eq zero of mul eq zero
-- statement:
--   The Flat Fibre Regular construction uses the eq zero of mul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim.lean#L109-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim.lean#L109-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatFibreRegular

theorem GlobalTheory.FlatFibreRegular.eq_zero_of_mul_eq_zero {A L : Type} [CommRing A] [IsNoetherianRing A] [CommRing L]
    [IsLocalRing L] [IsNoetherianRing L] [Algebra A L] [Module.Flat A L]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s))
    (hJ : 𝔭.map (algebraMap A L) ≠ ⊤)
    (g : L) (hg : ∀ y, g * y ∈ 𝔭.map (algebraMap A L) → y ∈ 𝔭.map (algebraMap A L))
    (y : L) (hgy : g * y = 0) : y = 0 := by sorry
