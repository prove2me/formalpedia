-- Prove2me | Theorems.Thm_GlobalTheory_finite_support_admissible
-- name    : GlobalTheory.finite_support_admissible
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:56:14.303846+00:00
-- url     : https://prove2.me/theorems/37a682a5-39f2-46f4-81a5-3b89c524df7e
-- title:
--   Global Theory: finite support admissible
-- statement:
--   The Global Theory construction uses the finite support admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteSupportAdmissible.lean#L270-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteSupportAdmissible.lean#L270-L337

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteSupportAdmissible
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
open NumberField
open scoped TensorProduct
attribute [local instance] _root_.ReciprocityTheory.ChartRestriction.G.T0.resAlg

theorem GlobalTheory.finite_support_admissible :
    (∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D : ℕ) (x : Fin D → Ω), (⊤ : IntermediateField K Ω).FG → Algebra.trdeg K Ω = D → ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) | _root_.ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v ∧ v g ≠ 0 ∧ ∃ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ∀ p : MvPolynomial (Fin D) (𝓞 K), 0 ≤ v (MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p) ∧ (0 < v (MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p) ↔ ∀ m, p.coeff m ∈ la.asIdeal)}.Finite) → (∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (t : Ω), (⊤ : IntermediateField F Ω).FG → Algebra.trdeg F Ω = 1 → Transcendental F t → ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) | _root_.ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v ∧ _root_.ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn F v ∧ 0 ≤ v t ∧ v g ≠ 0}.Finite) → ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : _root_.ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A), ∀ c : ι, 1 ≤ d.D → (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → (∀ G, Module.finrank (Ω c) (𝒜 c G) = 1) → (∀ j, d.w j c ∈ 𝒜 c d.wL) → d.w (d.jc c) c ≠ 0 → _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c → (∀ g : Ω c, g ≠ 0 → {v | d.admitted c v ∧ v g ≠ 0}.Finite) ∧ ∀ (G : WT) (e : A c) (S : Finset (Ω c)), e ∈ 𝒜 c G → e ≠ 0 → (∀ v, d.admitted c v → ∀ a : Ω c, a ≠ 0 → ((d.ord c v G (a • e) : ℤ) : WithTop ℤ) = v a + (d.ord c v G e : WithTop ℤ)) → (∀ v, d.admitted c v → (∀ s ∈ S, 0 ≤ v s) → d.ord c v G e = 0) → ∀ f ∈ 𝒜 c G, f ≠ 0 → {v | d.admitted c v ∧ d.ord c v G f ≠ 0}.Finite := by sorry
