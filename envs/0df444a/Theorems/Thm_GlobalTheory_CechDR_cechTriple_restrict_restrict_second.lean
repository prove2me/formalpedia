-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_cechTriple_restrict_restrict_second
-- name    : GlobalTheory.CechDR.cechTriple_restrict_restrict_second
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:28:35.669962+00:00
-- url     : https://prove2.me/theorems/d072b5b2-5a7c-4c34-b12b-6ca12149d49e
-- title:
--   Cech DR: cech Triple restrict restrict second
-- statement:
--   The Cech DR construction uses the cech Triple restrict restrict second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechTripleRestrictCompositeInjectiveSecond.lean#L353-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechTripleRestrictCompositeInjectiveSecond.lean#L353-L357

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

theorem GlobalTheory.CechDR.cechTriple_restrict_restrict_second (a : HH2 s'') :
    pullHyp2 (cechTripleRestrictFirst ψ φ s'') (pullHyp2 (pairRes ψ s'') a) =
      pullHyp2 (cechTripleRestrictComposite ψ φ s'') (pullHyp2 (pairRes (ψ ≫ φ) s'') a) := by sorry
