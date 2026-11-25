-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_cechTripleRestrictComposite_pairRes_first
-- name    : GlobalTheory.CechDR.cechTripleRestrictComposite_pairRes_first
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:48.479665+00:00
-- url     : https://prove2.me/theorems/53eff0ec-4607-499b-90e6-01a613315ad0
-- title:
--   Cech DR: cech Triple Restrict Composite pair Res first
-- statement:
--   The Cech DR construction uses the cech Triple Restrict Composite pair Res first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechTripleRestrictCompositeInjectiveSecond.lean#L277-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechTripleRestrictCompositeInjectiveSecond.lean#L277-L281

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
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
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite GlobalTheory.CatCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open FormExt FormExtJ
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
variable {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
variable (ψ φ)
variable {ψ φ}
variable (ψ φ)

theorem GlobalTheory.CechDR.cechTripleRestrictComposite_pairRes_first (s'' : X'' ⟶ Sp R'') (c : HH1 s'') :
    pullHyp1 (cechTripleRestrictComposite ψ φ s'') (pullHyp1 (pairRes (ψ ≫ φ) s'') c) =
      pullHyp1 (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))) c := by sorry
