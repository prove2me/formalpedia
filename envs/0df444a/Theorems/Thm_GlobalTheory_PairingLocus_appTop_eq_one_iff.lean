-- Prove2me | Theorems.Thm_GlobalTheory_PairingLocus_appTop_eq_one_iff
-- name    : GlobalTheory.PairingLocus.appTop_eq_one_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:41:06.663782+00:00
-- url     : https://prove2.me/theorems/f3829db4-1c85-4c5e-a6f5-672fb29c811b
-- title:
--   Pairing Locus: app Top eq one iff
-- statement:
--   The Pairing Locus construction uses the app Top eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsClopenOfIsLocallyNoetherian.lean#L50-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsClopenOfIsLocallyNoetherian.lean#L50-L63

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

theorem GlobalTheory.PairingLocus.appTop_eq_one_iff {X Y : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) (h : Y ⟶ X) :
    h.appTop.hom e = 1 ↔ Set.range h ⊆ X.basicOpen e := by sorry
