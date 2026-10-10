-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_active_tail_sliced_profile_comparison_with_scales
-- name    : OAI.Erdos3.exists_active_tail_sliced_profile_comparison_with_scales
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:52:02.381564+00:00
-- url     : https://prove2.me/theorems/d04662c3-b5aa-445c-b3af-e464c4a9f1ca
-- title:
--   Active-tail sliced profile comparison with explicit radius and tolerance
-- statement:
--   Let $W$ be a measurable space, $D,G,Z,\alpha$ finite types ($\alpha$ with decidable equality), $B\colon D\to$ Type a family of finite types, $h\colon D\to\mathbb N$ with $h(d)>0$ for all $d$, $P$ a decidable predicate on $D$, and `extra` $\colon G\to\mathrm{Option}\,\alpha\to Z$. For each $d$ with $\neg P(d)$ let $O(d)$ be a nonempty finite type, with injective maps `sets d` $\colon O(d)\to$ `Finset α` whose values have at most $h(d)$ elements, and injective maps `block d` $\colon O(d)\to B(d)$. Let $\psi\colon\mathbb R\to\mathbb R$ be $C^\infty$ with values in $[0,1]$, $\psi(t)=0$ for $|t|\le1$ and $\psi(t)=1$ for $|t|\ge2$; let $A,T\ge0$ with $\psi$ $A$-Lipschitz and `Real.smoothTransition` $T$-Lipschitz; let `degree` be a natural number with $h(d)\le$ `degree` for all $d$; and let $\delta,E$ be reals with $0<\delta\le1$ and $E>0$. Then there exists $\rho\ge0$ with $0<\rho\le1$ and $\rho=$ `partitionedAffineSourceRadius h P A T δ E`, and there exists a real $t$ with $0<t\le1$ and $t=$ `partitionedAffineSourceTolerance h P A T degree δ E` (both real numbers defined from OpenAI's `jointAffineSourceRadius` and `jointAffineCoefficientTolerance`), such that the following holds. For every $\tau\colon D\to\mathbb R$ with $|\tau_d|\le1$; every $z\colon W\to($`PartitionedProfileNoiseIndex G Z α B h P` $\to\mathbb R)$ with each coordinate measurable; all `center`, `width` $\colon$ `PrincipalAxisParameter (fun d => ¬P d)` $\to\mathbb R$ with $\delta\le|\mathrm{width}_i|$ and $|\mathrm{center}_i|+|\mathrm{width}_i|\le1$ for all $i$; every probability measure $\mu$ on $W$ with $|z(a)_j|\le1$ for all $j$ for $\mu$-almost every $a$; every $R\colon D\to\mathbb R$; and every measurable $f\colon W\times((\Sigma_d O(d))\to\mathbb R)\to\mathbb R$ with $\|f\|\le1$ everywhere, the absolute difference between
--   $$\int \texttt{activeAveragedSlicedProfileIdeal}\ Z\ h\ P\ \mathrm{sets}\ \rho\ \mathrm{center}\ \mathrm{width}\ (y)\cdot f\big(w,\ o\mapsto R_{o.1}\,y_o\big)\,d(\mu\otimes\mathrm{vol})(w,y)$$
--   and
--   $$\int f\Big(w,\ \texttt{partitionedAllocatedProfileJet}\ h\ P\ \mathrm{extra}\ \mathrm{sets}\ R\ t\ \big(\texttt{profileNoiseWithActive}\ h\ P\ (z(w))\ (\texttt{activeTailRescale}\ h\ P\ \tau\ u)\big)\ (i\mapsto\mathrm{center}_i+\mathrm{width}_i\,x_i)\Big)\,d\big((\mu\otimes\nu)\otimes\beta\big)((w,u),x)$$
--   is at most $E$. Here vol is Lebesgue measure on $(\Sigma_d O(d))\to\mathbb R$; $\nu=$ `unitCoefficientSource (ActiveProfileCoefficientIndex G B h P)` is the measure with density `smoothProductProfile` on functions from `ActiveProfileCoefficientIndex G B h P` (the pairs of an index $d$ with $\neg P(d)$ and a `SamplerCoefficientSlot G B h d`) to $\mathbb R$; $\beta=$ `jointBooleanSource (fun d => h d)` is a measure on functions from `PrincipalAxisParameter (fun d => ¬P d)` to $\mathbb R$; `activeAveragedSlicedProfileIdeal` is the mixture over $\nu$ of OpenAI's `activeSlicedProfileIdeal` (a real function on $(\Sigma_d O(d))\to\mathbb R$); `partitionedAllocatedProfileJet` is OpenAI's `partitionedProfileJet` with the scales $R_d/4$, `principalProfileSize` and `tailProfileSize`, a map to $(\Sigma_d O(d))\to\mathbb R$; `profileNoiseWithActive` replaces the coordinates of $z(w)$ at active indices ($\neg P$) by those of its second argument; and `activeTailRescale h P τ u` multiplies each coordinate of $u$ by a dilation factor determined by $\tau$ and `canonicalPrincipalExponent`.
--
--   Lean: `OAI.Erdos3.exists_active_tail_sliced_profile_comparison_with_scales` in `lean/OAI/Combinatorics/Progressions/Estimates/ActiveTailSlicedProfileComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B136` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/ActiveTailSlicedProfileComparison.lean#L11

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B136

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem exists_active_tail_sliced_profile_comparison_with_scales
    {W D G Z α : Type*} [MeasurableSpace W]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z)
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d.val)
    (block : ∀ d, O d → B d.val) (hblock : ∀ d, Function.Injective (block d))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    {δ E : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = partitionedAffineSourceRadius (B := B) (O := O) (α := α) h P A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = partitionedAffineSourceTolerance (G := G) (Z := Z) (B := B) (O := O) (α := α)
      h P A T degree δ E ∧
    ∀ τ : D → ℝ, (∀ d, |τ d| ≤ 1) →
    ∀ z : W → PartitionedProfileNoiseIndex G Z α B h P → ℝ,
    (∀ j, Measurable (fun a => z a j)) →
    ∀ (center width : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ),
    (∀ i, δ ≤ |width i|) → (∀ i, |center i| + |width i| ≤ 1) →
    ∀ μ : Measure W, IsProbabilityMeasure μ → (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
    ∀ (R : D → ℝ) (f : W × ((Σ d, O d) → ℝ) → ℝ),
    Measurable f → (∀ p, ‖f p‖ ≤ 1) →
    |(∫ p, activeAveragedSlicedProfileIdeal (G := G) (B := B) Z h P sets ρ center width p.2 *
        f (p.1, fun o => R o.1.val * p.2 o) ∂μ.prod volume) -
      ∫ p, f (p.1.1, partitionedAllocatedProfileJet h P extra sets R t
          (profileNoiseWithActive h P (z p.1.1) (activeTailRescale h P τ p.1.2))
          (fun i => center i + width i * p.2 i))
        ∂(μ.prod (unitCoefficientSource (ActiveProfileCoefficientIndex G B h P))).prod
          (jointBooleanSource (B := fun d : {d // ¬P d} => B d.val) (α := α) (fun d => h d.val))| ≤ E := by
  sorry

end Erdos3
end
end OAI
