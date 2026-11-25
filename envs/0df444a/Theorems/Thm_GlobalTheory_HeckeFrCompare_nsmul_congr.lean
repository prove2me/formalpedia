-- Prove2me | Theorems.Thm_GlobalTheory_HeckeFrCompare_nsmul_congr
-- name    : GlobalTheory.HeckeFrCompare.nsmul_congr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:56:28.702803+00:00
-- url     : https://prove2.me/theorems/f8d23de8-eb44-5b17-a9cc-8756b26a51b1
-- title:
--   Hecke Fr Compare: nsmul congr
-- statement:
--   The Hecke Fr Compare construction uses the nsmul congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L261-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L261-L265

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

theorem GlobalTheory.HeckeFrCompare.nsmul_congr {A M : Type} [AddCommGroup A] [Monoid M] (f : A → M) (hadd : ∀ a b, f (a + b) = f a * f b)
    (N : ℕ) (hN : ∀ a, f (N • a) = 1) {m n : ℕ} (h : m ≡ n [MOD N]) (a : A) : f (m • a) = f (n • a) := by sorry
