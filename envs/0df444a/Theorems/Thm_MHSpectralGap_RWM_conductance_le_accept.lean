-- Prove2me | Theorems.Thm_MHSpectralGap_RWM_conductance_le_accept
-- name    : MHSpectralGap.RWM.conductance_le_accept
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:14:07.037868+00:00
-- url     : https://prove2.me/theorems/6bcfc1e2-8e6a-45d8-a83e-28efeab71383
-- title:
--   p. 15 — for a Metropolis–Hastings kernel, C ≤ inf_{µ(A)≤1/2} ∫_A α(x)µ(dx)/µ(A) and C ≤ sup_{x∈B} α(x) whenever µ(B) ≤ 1/2
-- statement:
--   Let $Q$ be a Markov kernel on a measurable space $X$, $\alpha:X\times X\to[0,1]$ jointly measurable, $P$ the Metropolis–Hastings kernel (1.3) with proposal $Q$ and acceptance $\alpha$, and $\mu$ a probability measure on $X$. Write $\mathsf C$ for the conductance of $P$ with respect to $\mu$ and $\alpha(x)=\int\alpha(x,y)\,Q(x,dy)$. Then
--
--   $$
--   \mathsf C\;\le\;\inf_{0<\mu(A)\le 1/2}\frac{\int_A\alpha(x)\,\mu(dx)}{\mu(A)},
--   $$
--
--   and, for every measurable set $B$ with $0<\mu(B)\le\tfrac12$,
--
--   $$
--   \mathsf C\;\le\;\sup_{x\in B}\alpha(x).
--   $$
--
--   A Metropolis–Hastings chain can leave a set only by accepting a proposal, so the flow out of a set is bounded by the acceptance probability. These are the bounds that make Proposition 2.16's (2.8) work.
--
--   **Formalization Note** As in the definition of $\mathsf C$, the infimum is over measurable $A$ with $0<\mu(A)\le\tfrac12$, and $0<\mu(B)$ is required of $B$ (the paper writes only $\mu(B)\le\tfrac12$; for $\mu(B)=0$ the supremum over $B$ says nothing about $\mathsf C$). All quantities are in $[0,\infty]$.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 15, the displays after "Considering only the acceptance of the proposal gives rise to" and "In particular, for any set B such that µ(B) ≤ 1/2"

import Mathlib
import Definitions.Def_MHSpectralGap_RWM_MHKernel
import Definitions.Def_MHSpectralGap_RWM_L2Gap
import Definitions.Def_MHSpectralGap_RWM_Conductance

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.RWM

/-- The conductance displays of p. 15: considering only the acceptance of the proposal,
`C ≤ inf_{μ(A) ≤ 1/2} ∫_A α(x) μ(dx) / μ(A)`, and `C ≤ sup_{x ∈ B} α(x)` for every `B`
with `μ(B) ≤ 1/2`. -/
theorem conductance_le_accept {X : Type*} [MeasurableSpace X] (Q : ProbabilityTheory.Kernel X X)
    [ProbabilityTheory.IsMarkovKernel Q] (α : X → X → ℝ≥0∞)
    (hα : Measurable (Function.uncurry α)) (hα1 : ∀ x y, α x y ≤ 1)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    conductance (mhKernel Q α) μ ≤
        ⨅ (A : Set X) (_ : MeasurableSet A) (_ : 0 < μ A) (_ : μ A ≤ 1 / 2),
          (∫⁻ x in A, accBar Q α x ∂μ) / μ A ∧
      ∀ B : Set X, MeasurableSet B → 0 < μ B → μ B ≤ 1 / 2 →
        conductance (mhKernel Q α) μ ≤ ⨆ x ∈ B, accBar Q α x := by sorry

end MHSpectralGap.RWM
