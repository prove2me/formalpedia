-- Prove2me | Theorems.Thm_GlobalTheory_PairingLocus_pow_eq_one
-- name    : GlobalTheory.PairingLocus.pow_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:10.428933+00:00
-- url     : https://prove2.me/theorems/3c887dfb-94c0-4bf0-ac08-b1f417adaff6
-- title:
--   Pairing Locus: pow eq one
-- statement:
--   The Pairing Locus construction uses the pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsClopenOfIsLocallyNoetherian.lean#L76-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsClopenOfIsLocallyNoetherian.lean#L76-L86

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

theorem GlobalTheory.PairingLocus.pow_eq_one (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {x y : T ⟶ P.A}
    (hx : x ^ k = 1) {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by sorry
