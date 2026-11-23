-- Prove2me | Theorems.Thm_GlobalTheory_CardQuotientPow_main
-- name    : GlobalTheory.CardQuotientPow.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:42.392325+00:00
-- url     : https://prove2.me/theorems/4c95f300-c75b-4a43-92ad-1121e4b51bf2
-- title:
--   Card Quotient Pow: main
-- statement:
--   The Card Quotient Pow construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardQuotPow.lean#L34-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardQuotPow.lean#L34-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardQuotientPow
open Module Submodule

theorem GlobalTheory.CardQuotientPow.main {R M ι : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Fintype ι] (b : Module.Basis ι R M) {p : R}
    (hp : Irreducible p) (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    ∃ m : ℕ, Associated (LinearMap.det φ) (p ^ m) ∧
      Nat.card (M ⧸ LinearMap.range φ) = Nat.card (R ⧸ Ideal.span {p}) ^ m := by sorry
