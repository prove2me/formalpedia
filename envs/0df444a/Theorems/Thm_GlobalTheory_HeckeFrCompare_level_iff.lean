-- Prove2me | Theorems.Thm_GlobalTheory_HeckeFrCompare_level_iff
-- name    : GlobalTheory.HeckeFrCompare.level_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:46:10.296874+00:00
-- url     : https://prove2.me/theorems/c932acf5-0c57-4045-a8f7-67b2de267a2b
-- title:
--   Hecke Fr Compare: level iff
-- statement:
--   The Hecke Fr Compare construction uses the level iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L284-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L284-L292

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem GlobalTheory.HeckeFrCompare.level_iff {A M P P' : Type} [AddCommGroup A] [Monoid M] (f : A → M) (hadd : ∀ a b, f (a + b) = f a * f b)
    (N : ℕ) (hN : ∀ a, f (N • a) = 1) {p : ℕ} (hp : p.Coprime N) (hN0 : N ≠ 0) (i : M → P) (i' : M → P')
    (g : P → P') :
    (∀ p' : ℕ, p * p' ≡ 1 [MOD N] → ∀ a, g (i (f (p' • a))) = i' (f a)) ↔ ∀ a, g (i (f a)) = i' (f (p • a)) := by sorry
