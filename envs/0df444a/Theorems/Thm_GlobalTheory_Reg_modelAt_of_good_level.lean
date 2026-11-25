-- Prove2me | Theorems.Thm_GlobalTheory_Reg_modelAt_of_good_level
-- name    : GlobalTheory.Reg.modelAt_of_good_level
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:10.735094+00:00
-- url     : https://prove2.me/theorems/7489807b-33a0-4fa7-bb72-a8a40747309f
-- title:
--   Reg: model At of good level
-- statement:
--   The Reg construction uses the model At of good level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsValuationSubringComapEqNonunits.lean#L74-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsValuationSubringComapEqNonunits.lean#L74-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringComapEqNonunits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.Reg

theorem GlobalTheory.Reg.modelAt_of_good_level : PartI → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (Xo : ∀ l : Level H, Moduli Dw l) (l : Level H) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)), (∀ p : ℕ, p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p) → ModelAt (Xo l) c la := by sorry
