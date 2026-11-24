-- Prove2me | Theorems.Thm_GlobalTheory_ValMul_value_mul_eq
-- name    : GlobalTheory.ValMul.value_mul_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:50:25.876278+00:00
-- url     : https://prove2.me/theorems/f3bf6ed6-5899-41b1-a090-a0a2fa81a8ca
-- title:
--   Val Mul: value mul eq
-- statement:
--   The Val Mul construction uses the value mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetMul.lean#L31-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetMul.lean#L31-L174

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_AbsNormEqProdCmTypeSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IndexRangeMulVecLinEqAbsNormDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.ValMul
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.ValMul.value_mul_eq : ((∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ∀ A : Matrix ι ι (𝓞 E), A.det ≠ 0 → ((∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 ((fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b) a k)))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 ((fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b) a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range (fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b))).toAddSubgroup)) : ℝ)) = ((∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ)))) := by sorry
