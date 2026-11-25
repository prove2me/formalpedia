-- Prove2me | Theorems.Thm_GlobalTheory_nabValN_harmonic_gauge_independent
-- name    : GlobalTheory.nabValN_harmonic_gauge_independent
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:11:40.148393+00:00
-- url     : https://prove2.me/theorems/6f34de52-78fa-5f50-974f-e074a3c90bf3
-- title:
--   Global Theory: nab Val N harmonic gauge independent
-- statement:
--   The Global Theory construction uses the nab Val N harmonic gauge independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/HarmonicValueCopiesGaugeIndependent.lean#L76-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/HarmonicValueCopiesGaugeIndependent.lean#L76-L90

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
open GlobalTheory
open HarmCopies PowGerm

theorem GlobalTheory.nabValN_harmonic_gauge_independent :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B a).mulVec (u l) = σ l.1 a • u l) → ∀ (n : ℕ) (P : MvPolynomial (Letter T r n) k), P ∈ harmK r n k cc isX (fun _ => 1) → ∀ (w0 : O) (q : ℕ) (f : PS k n d), nabValN B k h w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B k h' w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P := by sorry
