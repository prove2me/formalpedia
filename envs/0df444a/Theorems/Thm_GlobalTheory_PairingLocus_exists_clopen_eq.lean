-- Prove2me | Theorems.Thm_GlobalTheory_PairingLocus_exists_clopen_eq
-- name    : GlobalTheory.PairingLocus.exists_clopen_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:41:43.365886+00:00
-- url     : https://prove2.me/theorems/cf062e6c-e211-4559-9114-e1f0f130abde
-- title:
--   Pairing Locus: exists clopen eq
-- statement:
--   The Pairing Locus construction uses the exists clopen eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsClopenOfIsLocallyNoetherian.lean#L65-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsClopenOfIsLocallyNoetherian.lean#L65-L74

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

theorem GlobalTheory.PairingLocus.exists_clopen_eq {X : Scheme.{0}} {n : ℕ} (hn : IsUnit (n : Γ(X, ⊤))) {c c₀ : Γ(X, ⊤)ˣ}
    (hc : c ^ n = 1) (hc₀ : c₀ ^ n = 1) :
    ∃ U : X.Opens, IsClosed (U : Set X) ∧ ∀ (Y : Scheme.{0}) (h : Y ⟶ X),
      Units.map h.appTop.hom.toMonoidHom c = Units.map h.appTop.hom.toMonoidHom c₀ ↔ Set.range h ⊆ U := by sorry
