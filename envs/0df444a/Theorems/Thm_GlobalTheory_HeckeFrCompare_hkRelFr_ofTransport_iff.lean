-- Prove2me | Theorems.Thm_GlobalTheory_HeckeFrCompare_hkRelFr_ofTransport_iff
-- name    : GlobalTheory.HeckeFrCompare.hkRelFr_ofTransport_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:48:53.268559+00:00
-- url     : https://prove2.me/theorems/50057446-ea14-4b18-a7ab-81ea8b0e186c
-- title:
--   Hecke Fr Compare: hk Rel Fr of Transport iff
-- statement:
--   The Hecke Fr Compare construction uses the hk Rel Fr of Transport iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L409-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HkRelFrOfTransportIff.lean#L409-L412

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

theorem GlobalTheory.HeckeFrCompare.hkRelFr_ofTransport_iff (h : IsSplitOff l 𝔓 p) (i : ℕ) (tr : Transport Xo c) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) 𝔓 p i Ω y) (z : FrPt Xo c Ω) :
    hkRelFr 𝔓 p i (ofTransport tr) Ω y C z ↔ IsHeckePt Xo c tr h i Ω y C z := by sorry
