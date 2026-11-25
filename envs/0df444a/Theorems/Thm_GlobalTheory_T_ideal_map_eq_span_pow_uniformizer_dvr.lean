-- Prove2me | Theorems.Thm_GlobalTheory_T_ideal_map_eq_span_pow_uniformizer_dvr
-- name    : GlobalTheory.T.ideal_map_eq_span_pow_uniformizer_dvr
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:21.948805+00:00
-- url     : https://prove2.me/theorems/35f4293b-ff7d-5a87-9fd5-a082bbc3e810
-- title:
--   T: ideal map eq span pow uniformizer dvr
-- statement:
--   The T construction uses the ideal map eq span pow uniformizer dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdealMapEqSpanPowUniformizerDvrStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdealMapEqSpanPowUniformizerDvrStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdealMapEqSpanPowUniformizerDvr
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdealMapEqSpanPowUniformizerDvrStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ideal_map_eq_span_pow_uniformizer_dvr : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W), Function.Injective f → ∀ (ϖ : V) (w : W) (e a : ℕ) (I : Ideal V), Irreducible ϖ → Irreducible w → Associated (f ϖ) (w ^ e) → I.map f = Ideal.span {w ^ a} → ∃ b : ℕ, e * b = a ∧ I = Ideal.span {ϖ ^ b} := by sorry
