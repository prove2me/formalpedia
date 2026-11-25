-- Prove2me | Theorems.Thm_GlobalTheory_FlatFibreRegular_mem_map_mul_of_mul_mem
-- name    : GlobalTheory.FlatFibreRegular.mem_map_mul_of_mul_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:42:05.875402+00:00
-- url     : https://prove2.me/theorems/45d3978e-a044-4fe7-a2d3-f0a1b4ae8b15
-- title:
--   Flat Fibre Regular: mem map mul of mul mem
-- statement:
--   The Flat Fibre Regular construction uses the mem map mul of mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim.lean#L48-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim.lean#L48-L107

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

theorem GlobalTheory.FlatFibreRegular.mem_map_mul_of_mul_mem {A L : Type} [CommRing A] [CommRing L] [Algebra A L] [Module.Flat A L]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s))
    (g : L) (hg : ∀ y, g * y ∈ 𝔭.map (algebraMap A L) → y ∈ 𝔭.map (algebraMap A L))
    (I : Ideal A) (hI : I.FG) (y : L) (hy : y ∈ I.map (algebraMap A L))
    (hgy : g * y ∈ (I * 𝔭).map (algebraMap A L)) : y ∈ (I * 𝔭).map (algebraMap A L) := by sorry
