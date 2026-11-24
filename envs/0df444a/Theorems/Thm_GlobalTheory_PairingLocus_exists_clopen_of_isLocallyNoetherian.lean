-- Prove2me | Theorems.Thm_GlobalTheory_PairingLocus_exists_clopen_of_isLocallyNoetherian
-- name    : GlobalTheory.PairingLocus.exists_clopen_of_isLocallyNoetherian
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:55.426844+00:00
-- url     : https://prove2.me/theorems/f1ddbea5-d4de-4838-addd-aa972f8ad86f
-- title:
--   Pairing Locus: exists clopen of is Locally Noetherian
-- statement:
--   The Pairing Locus construction uses the exists clopen of is Locally Noetherian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsClopenOfIsLocallyNoetherian.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsClopenOfIsLocallyNoetherian.lean#L111-L117

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

theorem GlobalTheory.PairingLocus.exists_clopen_of_isLocallyNoetherian (hL : Laws) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S)
    (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ) (hn : IsUnit (n : Γ(T.left, ⊤))) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (hc : c ^ n = 1) :
    ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
      WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U := by sorry
