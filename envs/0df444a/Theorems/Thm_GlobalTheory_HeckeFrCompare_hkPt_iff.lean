-- Prove2me | Theorems.Thm_GlobalTheory_HeckeFrCompare_hkPt_iff
-- name    : GlobalTheory.HeckeFrCompare.hkPt_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:03:42.201391+00:00
-- url     : https://prove2.me/theorems/148e7195-194e-5852-a603-a7ee4a5c650a
-- title:
--   Hecke Fr Compare: hk Pt iff
-- statement:
--   The Hecke Fr Compare construction uses the hk Pt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L379-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L379-L392

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

theorem GlobalTheory.HeckeFrCompare.hkPt_iff (h : IsSplitOff l 𝔓 p) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
    (sTr : ∀ (y z : FrPt Xo c Ω), (pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) → Prop)
    (y : FrPt Xo c Ω) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)) (z : FrPt Xo c Ω) :
    HkPt p sTr y C z ↔ ∃ ψ : Gx y.x ⟶ Gx z.x, IsHeckeIsog p C ψ ∧ (∀ τ j, IsLieImg p ψ (y.u τ j) (z.u τ j)) ∧
      sTr y z ((conj y.x z.x).symm ψ) := by sorry
