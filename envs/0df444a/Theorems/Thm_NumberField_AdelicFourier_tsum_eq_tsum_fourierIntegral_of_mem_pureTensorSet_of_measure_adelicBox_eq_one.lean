-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one
-- name    : NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/8d9ffef9-a535-5a61-917f-2b05e4393be0
-- title:
--   Adelic Poisson summation for pure tensors, normalised Haar measure
-- statement:
--   Let $F$ be a number field, and equip its adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F` with a measurable structure that is the Borel structure of its topology. Let $\mu$ be an additive Haar measure on $\mathbb{A}_F$ normalised so that $\mu(\mathrm{adelicBox}\,F) = 1$, where $\mathrm{adelicBox}\,F$ consists of those adeles whose infinite component lies in the preimage, under the identification of the infinite adeles with the mixed space, of the fundamental domain of the lattice basis coming from the canonical embedding of $F$, and whose finite component is integral at every height-one prime of $\mathcal{O}_F$. Let $\psi : \mathbb{A}_F \to \mathbb{C}^\times$ be an additive character which is global in the sense that it is trivial on every principal adele $\iota\alpha$, $\alpha \in F$, is continuous, and is not identically $1$. Let $f : \mathbb{A}_F \to \mathbb{C}$ be a pure tensor, i.e. $f(x) = g(x_\infty)h(x_{\mathrm{fin}})$ for some Schwartz function $g$ on the mixed space of $F$ (evaluated through the identification of the infinite adeles with that space) and some locally constant, compactly supported $h$ on the finite adele ring. Then $$\sum_{\xi \in F} f(\iota\xi) = \sum_{\xi \in F} \hat{f}(\iota\xi), \qquad \hat{f}(w) = \int_{\mathbb{A}_F} \psi(-(vw))f(v)\,\mathrm{d}\mu(v),$$ both sides being unconditional sums over $F$ in Lean's sense.
--
--   This is adelic Poisson summation (Tate's thesis, Theorem 4.2.1; Weil, Basic Number Theory VII §2) for pure tensor test functions, in the normalised case where the measure of the adelic box is $1$, so that no volume factor appears on the right. It is the form from which the statement for an arbitrary additive Haar measure, [`NumberField.AdelicFourier.tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet`](thm.html#NumberField.AdelicFourier.tsum_eq_inv_measure_mul_tsum_fourierIntegral_of_mem_pureTensorSet), is obtained by rescaling $\mu$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one.lean

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm

theorem NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (hμB : μ (AdelicBox.adelicBox F) = 1)
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by sorry
