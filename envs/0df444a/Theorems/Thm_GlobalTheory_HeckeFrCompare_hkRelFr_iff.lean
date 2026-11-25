-- Prove2me | Theorems.Thm_GlobalTheory_HeckeFrCompare_hkRelFr_iff
-- name    : GlobalTheory.HeckeFrCompare.hkRelFr_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:46:07.908059+00:00
-- url     : https://prove2.me/theorems/2d22b0b9-10fc-486b-a7c1-34bc787f5f96
-- title:
--   Hecke Fr Compare: hk Rel Fr iff
-- statement:
--   The Hecke Fr Compare construction uses the hk Rel Fr iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L394-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L394-L403

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

theorem GlobalTheory.HeckeFrCompare.hkRelFr_iff (h : IsSplitOff l 𝔓 p) (i : ℕ)
    (sTr : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y z : FrPt Xo c Ω),
      (pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x) → Prop)
    (tr : Transport Xo c) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω)
    (C : hkKer (Xo := Xo) 𝔓 p i Ω y) (z : FrPt Xo c Ω)
    (htr : ∀ ψ, sTr Ω y z ψ ↔ tr Ω y.x z.x (conj y.x z.x ψ) y.s z.s) :
    hkRelFr 𝔓 p i sTr Ω y C z ↔ IsHeckePt Xo c tr h i Ω y C z := by sorry
