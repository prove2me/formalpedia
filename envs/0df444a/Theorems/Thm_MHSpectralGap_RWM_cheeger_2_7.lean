-- Prove2me | Theorems.Thm_MHSpectralGap_RWM_cheeger_2_7
-- name    : MHSpectralGap.RWM.cheeger_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:14:06.790984+00:00
-- url     : https://prove2.me/theorems/1a27ef5b-801e-49ec-8619-9bbdb0848a2b
-- title:
--   (2.7), p. 14 — Cheeger's inequality 1 − β ≤ 2C for a µ-reversible Markov kernel (cited)
-- statement:
--   Let $P$ be a Markov kernel on a measurable space $X$ that is reversible with respect to a probability measure $\mu$, i.e. $\int_A P(x,B)\,d\mu(x)=\int_B P(x,A)\,d\mu(x)$ for all measurable $A,B$. Let $\beta=\|P\|_{L^2_0\to L^2_0}$ (Definition 2.7) and let $\mathsf C$ be the conductance (2.6). Then
--
--   $$
--   1-\beta\;\le\;2\,\mathsf C .
--   $$
--
--   This is Cheeger's inequality in its upper direction, cited in the paper from Lawler and Sokal (1988) and Sinclair and Jerrum (1989) and not proved there. It converts an upper bound on the conductance into an upper bound on the spectral gap, and it is the first step of both parts of Theorem 2.17.
--
--   **Formalization Note** The inequality is stated in $[0,\infty]$: the left side is $\max(1-\beta,0)$ and $\mathsf C=+\infty$ when no measurable set has $0<\mu(A)\le\tfrac12$ (then the claim is empty, as it should be).
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 14, display (2.7) (cited from Lawler and Sokal 1988; Sinclair and Jerrum 1989)

import Mathlib
import Definitions.Def_MHSpectralGap_RWM_MHKernel
import Definitions.Def_MHSpectralGap_RWM_L2Gap
import Definitions.Def_MHSpectralGap_RWM_Conductance

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.RWM

/-- Cheeger's inequality (2.7), p. 14 (cited from Lawler–Sokal 1988, Sinclair–Jerrum 1989):
for a `μ`-reversible Markov kernel `P` and a probability measure `μ`, `1 − β ≤ 2C`. -/
theorem cheeger_2_7 {X : Type*} [MeasurableSpace X] (P : ProbabilityTheory.Kernel X X)
    [ProbabilityTheory.IsMarkovKernel P] (μ : Measure X) [IsProbabilityMeasure μ]
    (hrev : P.IsReversible μ) :
    ENNReal.ofReal (1 - l2Beta P μ) ≤ 2 * conductance P μ := by sorry

end MHSpectralGap.RWM
