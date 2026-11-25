-- Prove2me | Theorems.Thm_GlobalTheory_aemeasurable_finsum_section
-- name    : GlobalTheory.aemeasurable_finsum_section
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:11:59.210719+00:00
-- url     : https://prove2.me/theorems/a268cb44-c984-5525-bd3b-07712bdb29b0
-- title:
--   Global Theory: aemeasurable finsum section
-- statement:
--   The Global Theory construction uses the aemeasurable finsum section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AemeasurableFinsumSection.lean#L179-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AemeasurableFinsumSection.lean#L179-L239

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AemeasurableFinsumSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open SectionSum MeasureTheory

theorem GlobalTheory.aemeasurable_finsum_section :
    (∀ (K : Type) [Field K] [Countable K] (sg : K →+* ℂ) (D N : ℕ), ∀ᵐ t ∂(MeasureTheory.Measure.pi fun _ : Fin D => (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere), ∀ p : MvPolynomial (Fin D × Fin (N + 1)) K, p ≠ 0 → MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p ≠ 0) → (∀ (K : Type) [Field K] [CharZero K] (σ : Type) [Fintype σ] (L : Type) [Field L] [Algebra (FractionRing (MvPolynomial σ K)) L] [FiniteDimensional (FractionRing (MvPolynomial σ K)) L] (sg : K →+* ℂ) (m : ℕ) (b : Fin m → L) (Nf : (Fin m → ℂ) → ℝ), Measurable Nf → ∃ Φ : (σ → ℂ) → ℝ, Measurable Φ ∧ ∀ t : σ → ℂ, (∀ p : MvPolynomial σ K, p ≠ 0 → MvPolynomial.eval₂ sg t p ≠ 0) → Φ t = ∑ᶠ P ∈ {P : L →+* ℂ | ∀ p : MvPolynomial σ K, P (algebraMap (FractionRing (MvPolynomial σ K)) L (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p)) = MvPolynomial.eval₂ sg t p}, Nf (fun i => P (b i))) → (∀ (K Ω L : Type) [Field K] [Field Ω] [Algebra K Ω] [Field L] [Algebra K L] (D N : ℕ) (j₀ : Fin (N + 1)) (x : Fin N → Ω) (τ : TVar D N → L) (φ : Ω →ₐ[K] L), Algebra.trdeg K Ω = D → AlgebraicIndependent K τ → (∀ i : Fin D, τ (i.succ, j₀) + ∑ k, τ (i.succ, j₀.succAbove k) * φ (x k) = 0) → ∃! P : OmS Ω D N →+* L, (∀ a : Ω, P (algebraMap Ω (OmS Ω D N) a) = φ a) ∧ ∀ p, P (sImg j₀ x p) = τ p) → ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), ∀ c : ι, (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → d.w (d.jc c) c ≠ 0 → (∃ J : Fin d.D → Fin d.N, LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))) → ∀ (sg : K →+* ℂ) (m : ℕ) (a : Fin m → Ω c) (Nf : (Fin m → ℂ) → ℝ) (h : (Ω c →+* ℂ) → ℝ), Measurable Nf → (∀ P ∈ PT (Ω := Ω c) sg, h P = Nf (fun i => P (a i))) → AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 => ∑ᶠ P ∈ d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j), h P) d.sphMeasure := by sorry
