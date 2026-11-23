-- Prove2me | Theorems.Thm_GlobalTheory_PairingLocus_exists_clopen_of_weilIs
-- name    : GlobalTheory.PairingLocus.exists_clopen_of_weilIs
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:08.509075+00:00
-- url     : https://prove2.me/theorems/bf48c9b9-54f3-4ebb-8fec-bf531c1d9845
-- title:
--   Pairing Locus: exists clopen of weil Is
-- statement:
--   The Pairing Locus construction uses the exists clopen of weil Is property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsClopenOfIsLocallyNoetherian.lean#L88-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsClopenOfIsLocallyNoetherian.lean#L88-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsClopenOfIsLocallyNoetherian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLocus

theorem GlobalTheory.PairingLocus.exists_clopen_of_weilIs (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) {T : Over S}
    {x y : T ⟶ P.A} {c c₀ : Γ(T.left, ⊤)ˣ} (hn : IsUnit (n : Γ(T.left, ⊤))) (hx : x ^ n = 1) (hc : c ^ n = 1)
    (h₀ : WeilIs P.A P.L n x y c₀) :
    ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
      WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U := by sorry
