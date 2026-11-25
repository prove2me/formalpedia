-- Prove2me | Theorems.Thm_GlobalTheory_HarmCopies_col_sum_eq_zero
-- name    : GlobalTheory.HarmCopies.col_sum_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:01:49.664172+00:00
-- url     : https://prove2.me/theorems/27516e9f-57e5-4436-9fe0-1dff5a543c3d
-- title:
--   Harm Copies: col sum eq zero
-- statement:
--   The Harm Copies construction uses the col sum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/HarmonicValueCopiesGaugeIndependent.lean#L51-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/HarmonicValueCopiesGaugeIndependent.lean#L51-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_HarmonicValueCopiesGaugeIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.HarmCopies
open GlobalTheory.PowGerm

theorem GlobalTheory.HarmCopies.col_sum_eq_zero {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop}
    (Q : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)
    (hQ : MvPolynomial.rename (letterEquiv T r n) Q ∈ harmK r n k cc isX (fun _ => 1))
    (τ : T) (hτ : isX τ) (i : Fin (r τ)) (i' : Fin (r (cc τ))) :
    ∑ b : Fin n, MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b)
      (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) Q) = 0 := by sorry
