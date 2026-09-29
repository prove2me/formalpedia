-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
-- name    : NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/5fb13ca3-7ce4-5f69-afb5-f2da01dead0d
-- title:
--   Adelic Poisson summation for pure tensors, normalised
-- statement:
--   Let $F$ be a number field, and fix a measurable structure on the adele ring $\mathbb{A}_F = \mathbb{A}_{\mathcal{O}_F,F}$ (Mathlib's `AdeleRing (𝓞 F) F`, the product of the infinite adele ring with the finite adele ring) which is Borel for its topology. Let $\mu$ be an additive Haar measure on $\mathbb{A}_F$ normalised by $\mu(B)=1$, where $B$ is the adelic box `AdelicBox.adelicBox F` consisting of those adeles whose infinite component is carried by the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace F` into the fundamental domain of the lattice basis `mixedEmbedding.latticeBasis F` of the mixed space, and whose finite component lies in $v$-adic integers at every $v$ in the height-one spectrum of $\mathcal{O}_F$. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ which is global in the sense that it is continuous, not identically $1$, and satisfies $\psi(\iota(\alpha))=1$ for every $\alpha \in F$, $\iota$ being the diagonal embedding $F \to \mathbb{A}_F$; assume moreover that its archimedean component is the standard one, namely $\psi(x,0) = e^{2\pi i \operatorname{Tr}(x)}$ for all $x$ in the infinite adele ring, the trace being that of the mixed space over $\mathbb{R}$ evaluated on the image of $x$, and $e^{2\pi i(\cdot)}$ being `Real.fourierChar`. Finally let $f : \mathbb{A}_F \to \mathbb{C}$ be a pure tensor, i.e. $f(x) = g(x_\infty)h(x_{\mathrm{f}})$ for some Schwartz function $g$ on the mixed space of $F$ (composed with `InfiniteAdeleRing.ringEquiv_mixedSpace F`) and some locally constant, compactly supported $h$ on the finite adele ring. Then $$\sum_{\xi \in F} f(\iota(\xi)) = \sum_{\xi \in F} \hat{f}(\iota(\xi)),$$ the sums being `tsum`s over the type $F$ and $\hat{f}(w) = \int_{\mathbb{A}_F} \psi(-(vw))f(v)\,d\mu(v)$.
--
--   This is the Poisson summation formula of Tate's thesis for the adele ring of a number field, restricted to pure tensors in the adelic Schwartz–Bruhat space, with both normalisations spelled out as hypotheses: the Haar measure is normalised by giving the adelic box volume $1$, and the character is pinned down by its archimedean component. It feeds the variant [`NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one`](thm.html#NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one), and ultimately the computation of Whittaker coefficients of adelic automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm

theorem NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (hμB : μ (AdelicBox.adelicBox F) = 1)
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by sorry
