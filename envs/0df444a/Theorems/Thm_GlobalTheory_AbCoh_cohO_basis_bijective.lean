-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_cohO_basis_bijective
-- name    : GlobalTheory.AbCoh.cohO_basis_bijective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:54:56.925301+00:00
-- url     : https://prove2.me/theorems/9b448343-b909-4b1e-9635-40407cca45fa
-- title:
--   Ab Coh: coh O basis bijective
-- statement:
--   The Ab Coh construction uses the coh O basis bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyBasisBijective.lean#L36-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyBasisBijective.lean#L36-L94

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

theorem GlobalTheory.AbCoh.cohO_basis_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (P : Type) [Preorder P] (G : P → X.affineOpens) (hG : Monotone G), (∀ (U : X.affineOpens) (x : X), x ∈ U.1 → ∃ a, x ∈ (G a).1 ∧ (G a).1 ≤ U.1) → (∀ (a b : P) (x : X), x ∈ (G a).1 → x ∈ (G b).1 → ∃ c, c ≤ a ∧ c ≤ b ∧ x ∈ (G c).1) → Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull2 ∧ (CohomZeroIsConstants (OAff s) → CohomZeroIsConstants (hG.functor.op ⋙ OAff s)) := by sorry
