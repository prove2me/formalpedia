-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_tri_pull_pullO
-- name    : GlobalTheory.CechDR.tri_pull_pullO
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:51:05.320493+00:00
-- url     : https://prove2.me/theorems/d5bc3ee1-28af-405e-afec-d0e53813a16f
-- title:
--   Cech DR: tri pull pull O
-- statement:
--   The Cech DR construction uses the tri pull pull O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyPullbackCompCupId.lean#L91-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyPullbackCompCupId.lean#L91-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupId
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CechDR
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {ψ : X'' ⟶ X'} {φ : X' ⟶ X}

theorem GlobalTheory.CechDR.tri_pull_pullO (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) :
    (∀ a : HO1 s, (cechTripleRestrictComposite ψ φ s'').pull1 ((pairPull h'').pull1 a) =
      (cechTriplePullbackSecond h').pull1 ((pairPull h).pull1 a)) ∧
    (∀ a : HO2 s, (cechTripleRestrictComposite ψ φ s'').pull2 ((pairPull h'').pull2 a) =
      (cechTriplePullbackSecond h').pull2 ((pairPull h).pull2 a)) ∧
    (∀ a : GlobForm s, pullGlob1 (cechTripleRestrictComposite ψ φ s'') (pullGlob1 (pairPull h'') a) =
      pullGlob1 (cechTriplePullbackSecond h') (pullGlob1 (pairPull h) a)) := by sorry
