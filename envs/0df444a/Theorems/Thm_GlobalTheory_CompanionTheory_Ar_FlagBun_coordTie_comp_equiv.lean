-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagBun_coordTie_comp_equiv
-- name    : GlobalTheory.CompanionTheory.Ar.FlagBun.coordTie_comp_equiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:13.702448+00:00
-- url     : https://prove2.me/theorems/7dae2c7a-085a-4a64-bd57-6ceb7149909f
-- title:
--   Flag Bun: coord Tie comp equiv
-- statement:
--   The Flag Bun construction uses the coord Tie comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/CoordTieCompEquiv.lean#L43-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/CoordTieCompEquiv.lean#L43-L60

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
open AlgebraicGeometry CategoryTheory
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {S : Type} {r : S → ℕ}

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.coordTie_comp_equiv {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {o : Type}
    [CommRing o] [Algebra o Ω] {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' ≃ κ) :
    CoordTie o ξ (x ∘ e) := by sorry
