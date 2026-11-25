-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_SpanCup_sum_append
-- name    : GlobalTheory.AbCoh.SpanCup.sum_append
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:06:09.309841+00:00
-- url     : https://prove2.me/theorems/54beda1d-ab18-4298-808d-c41ced4f9fc7
-- title:
--   Span Cup: sum append
-- statement:
--   The Span Cup construction uses the sum append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HyperH2GeneratedByCups.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HyperH2GeneratedByCups.lean#L16-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2SumOfCupsExactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2GeneratedByCups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.SpanCup

theorem GlobalTheory.AbCoh.SpanCup.sum_append {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (B : M →ₗ[R] N →ₗ[R] P) {n m : ℕ} (a : Fin n → M) (b : Fin n → N)
    (a' : Fin m → M) (b' : Fin m → N) :
    ∑ k, B (a k) (b k) + ∑ k, B (a' k) (b' k) = ∑ k, B (Fin.append a a' k) (Fin.append b b' k) := by sorry
