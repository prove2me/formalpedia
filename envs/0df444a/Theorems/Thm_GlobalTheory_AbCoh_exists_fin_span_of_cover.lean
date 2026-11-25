-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_exists_fin_span_of_cover
-- name    : GlobalTheory.AbCoh.exists_fin_span_of_cover
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:57:06.836948+00:00
-- url     : https://prove2.me/theorems/891bdd69-84f8-4dd2-8de2-a1ec248f2127
-- title:
--   Ab Coh: exists fin span of cover
-- statement:
--   The Ab Coh construction uses the exists fin span of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyBasisBijective.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyBasisBijective.lean#L14-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyBasisBijective
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
open GlobalTheory GlobalTheory.AbCoh

theorem GlobalTheory.AbCoh.exists_fin_span_of_cover {X : Scheme.{0}} (T : X.affineOpens) (B : Set Γ(X, T.1))
    (hB : ∀ x ∈ T.1, ∃ f ∈ B, x ∈ X.basicOpen f) :
    ∃ (n : ℕ) (b : Fin n → Γ(X, T.1)), Ideal.span (Set.range b) = ⊤ ∧ ∀ i, b i ∈ B := by sorry
