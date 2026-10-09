-- Prove2me | Theorems.Thm_MHSpectralGap_RWM_proposition_2_16
-- name    : MHSpectralGap.RWM.proposition_2_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:14:33.635535+00:00
-- url     : https://prove2.me/theorems/37108069-74bb-45e1-905b-6757472cfb1d
-- title:
--   Proposition 2.16, p. 15 — (2.8) 1 − β ≤ 2C ≤ 2 sup_{x∈B} α(x) for µ(B) ≤ 1/2 and (2.9) 1 − β ≤ 2C ≤ 2 inf_A ∫_A Q(x, Aᶜ)dµ/µ(A)
-- statement:
--   Let $Q$ be a Markov kernel on a measurable space $X$, $\alpha:X\times X\to[0,1]$ jointly measurable, and $P$ the Metropolis–Hastings kernel (1.3) with proposal $Q$ and acceptance probability $\alpha$. Let $\mu$ be a probability measure for which $P$ is reversible (the target of the Metropolis–Hastings algorithm). Let $\beta=\|P\|_{L^2_0\to L^2_0}$, $\mathsf C$ the conductance and $\alpha(x)=\int\alpha(x,y)Q(x,dy)$. Then:
--
--   1. **(2.8)** for every measurable $B$ with $0<\mu(B)\le\tfrac12$,
--   $$
--   1-\beta\;\le\;2\mathsf C\;\le\;2\sup_{x\in B}\alpha(x);
--   $$
--   2. **(2.9)**
--   $$
--   1-\beta\;\le\;2\mathsf C\;\le\;2\inf_{0<\mu(A)\le 1/2}\frac{\int_A Q(x,A^c)\,d\mu(x)}{\mu(A)}.
--   $$
--
--   The first bound is effective when proposals are rarely accepted, the second when proposals rarely leave a set; Theorem 2.17 uses the first for small step-size decay ($a<1$) and the second for $a\ge 1$.
--
--   **Formalization Note** The paper's chain also contains a middle term $1-\Lambda$, but $\Lambda$ is never defined in the paper; it is dropped. The conditions $0<\mu(B)$ and $0<\mu(A)$ are added (see the definition of the conductance). Reversibility of $P$ with respect to $\mu$ is the formal content of "a Metropolis–Hastings transition kernel for a target measure $\mu$". The second branch of (2.8), $2\mathsf C\le 2\mathbb E_\mu\alpha(x)$, is a separate item. Inequalities are in $[0,\infty]$, the left side being $\max(1-\beta,0)$.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 15, Proposition 2.16, displays (2.8) (first branch) and (2.9)

import Mathlib
import Definitions.Def_MHSpectralGap_RWM_MHKernel
import Definitions.Def_MHSpectralGap_RWM_L2Gap
import Definitions.Def_MHSpectralGap_RWM_Conductance

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.RWM

/-- Proposition 2.16, p. 15, (2.8) first branch and (2.9): for a Metropolis–Hastings kernel
`P = mhKernel Q α` reversible for the target `μ`,
`1 − β ≤ 2C ≤ 2 sup_{x ∈ B} α(x)` for every `B` with `0 < μ(B) ≤ 1/2`, and
`1 − β ≤ 2C ≤ 2 inf_{μ(A) ≤ 1/2} ∫_A Q(x, Aᶜ) dμ(x) / μ(A)`. -/
theorem proposition_2_16 {X : Type*} [MeasurableSpace X] (Q : ProbabilityTheory.Kernel X X)
    [ProbabilityTheory.IsMarkovKernel Q] (α : X → X → ℝ≥0∞)
    (hα : Measurable (Function.uncurry α)) (hα1 : ∀ x y, α x y ≤ 1)
    (μ : Measure X) [IsProbabilityMeasure μ] (hrev : (mhKernel Q α).IsReversible μ) :
    (∀ B : Set X, MeasurableSet B → 0 < μ B → μ B ≤ 1 / 2 →
      ENNReal.ofReal (1 - l2Beta (mhKernel Q α) μ) ≤ 2 * conductance (mhKernel Q α) μ ∧
        2 * conductance (mhKernel Q α) μ ≤ 2 * ⨆ x ∈ B, accBar Q α x) ∧
    (ENNReal.ofReal (1 - l2Beta (mhKernel Q α) μ) ≤ 2 * conductance (mhKernel Q α) μ ∧
      2 * conductance (mhKernel Q α) μ ≤
        2 * ⨅ (A : Set X) (_ : MeasurableSet A) (_ : 0 < μ A) (_ : μ A ≤ 1 / 2),
          (∫⁻ x in A, Q x Aᶜ ∂μ) / μ A) := by sorry

end MHSpectralGap.RWM
