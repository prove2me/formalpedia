-- Prove2me | Theorems.Thm_OAI_SecondPassArithmetic_full_uniform_canonicalSourceTail_bound
-- name    : OAI.SecondPassArithmetic.full_uniform_canonicalSourceTail_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:09:57.435651+00:00
-- url     : https://prove2.me/theorems/d63dbb12-dec2-450a-a673-afcf3a304041
-- title:
--   Second Pass Arithmetic: full uniform canonical Source Tail bound
-- statement:
--   The Second Pass Arithmetic construction uses the full uniform canonical Source Tail bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/CanonicalTailBounds.lean#L290-L426
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/CanonicalTailBounds.lean#L290-L426

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_RetainedDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalTailBounds
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

theorem OAI.SecondPassArithmetic.full_uniform_canonicalSourceTail_bound (ε:ℝ) (hε:0<ε) (A:ℕ):
    ∃(s:Finset (ℕ×ℕ)) (C:ℝ),0<C ∧
    ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal ActualEisensteinCubic.O))
      (a:CubeCoordinates ι→Finset ι→Ideal ActualEisensteinCubic.O→ℂ) (Ψ₁ Ψ₂:ActualEisensteinCubic.O→*ℂ)
      (m₁ m₂:ActualEisensteinCubic.O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ M₁ M₂ Ksrc K ell B F lengthScale:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<Ksrc → 0<K → 0<ell → 1≤B → 1≤F → 1≤lengthScale →
      ell*Real.exp M₁≤lengthScale → ell*Real.exp M₂≤lengthScale →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) →
      (∀t,g₁ t≠0→t≤M₁) → (∀t,g₂ t≠0→t≤M₂) →
      ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell‖≤
      C*B^(4+ε)*lengthScale^4*F*Γ*(G₁*G₂*Ksrc)*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*
        (1+lengthScale^3*B^4/Ksrc)^2/(1+(Ksrc/K)/Real.exp (M₁+M₂))^A := by sorry
