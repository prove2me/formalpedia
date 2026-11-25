-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_tri_res_pull1
-- name    : GlobalTheory.CechDR.tri_res_pull1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:22.270797+00:00
-- url     : https://prove2.me/theorems/01cbfd23-ddc9-4a35-a614-b9ba4bec91cd
-- title:
--   Cech DR: tri res pull1
-- statement:
--   The Cech DR construction uses the tri res pull1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechTripleRestrictCompositeInjectiveSecond.lean#L335-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechTripleRestrictCompositeInjectiveSecond.lean#L335-L339

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
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

theorem GlobalTheory.CechDR.tri_res_pull1 (h' : ψ ≫ s' = s'' ≫ spMap τ) (a : HH1 s') :
    pullHyp1 (cechTriplePullbackSecond (φ := φ) h') (pullHyp1 (pairRes φ s') a) =
      pullHyp1 (cechTripleRestrictFirst ψ φ s'') (pullHyp1 (pairPull h') a) := by sorry
