-- Prove2me | Theorems.Thm_GlobalTheory_HeckeFrCompare_idx_eq
-- name    : GlobalTheory.HeckeFrCompare.idx_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:50:03.407806+00:00
-- url     : https://prove2.me/theorems/44e32ddc-05c4-47ac-8a13-be31ae1115b8
-- title:
--   Hecke Fr Compare: idx eq
-- statement:
--   The Hecke Fr Compare construction uses the idx eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L376-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L376-L377

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
variable {c : Coeff l} {𝔓 : Ideal (𝓞 E)} {p : ℕ}

theorem GlobalTheory.HeckeFrCompare.idx_eq (h : IsSplitOff l 𝔓 p) (i : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    (y : FrPt Xo c Ω) : hkKer (Xo := Xo) 𝔓 p i Ω y = HeckeIdx Xo c h i Ω y := by sorry
