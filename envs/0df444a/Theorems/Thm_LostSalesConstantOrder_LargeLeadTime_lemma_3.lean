-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_lemma_3
-- name    : LostSalesConstantOrder.LargeLeadTime.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:45.526918+00:00
-- url     : https://prove2.me/theorems/b552babf-e41d-4f85-b84e-3a6ca4230517
-- title:
--   Lemma 3: the cost of L consecutive periods from state (x, 𝓘)
-- statement:
--   Consider the lost-sales system with lead time $L$, holding cost $h>0$, penalty $c>0$ and i.i.d. demands $D_t$ with law $\mathcal D$ (finite third moment, not deterministic). Fix a period $\tau$. For any admissible policy $\pi$, the expected cost of the $L$ periods $\tau,\dots,\tau+L-1$ is the expectation, over the state $(\mathbf x^\pi_\tau,I^\pi_\tau)$, of the expected cost of those periods for the system started in that state:
--   $$
--   \mathbb E\Big[\sum_{t=\tau}^{\tau+L-1}C^\pi_t\Big]=\mathbb E\big[\mathrm{windowCost}(\mathbf x^\pi_\tau,I^\pi_\tau)\big].
--   $$
--   Moreover, for every pipeline $\mathbf x$ and initial inventory $\mathcal I$,
--   $$
--   \mathrm{windowCost}(\mathbf x,\mathcal I)=h\sum_{k=1}^L\mathbb E\Big[\max_{j=0,\dots,k}\Big(\sum_{i=k+1-j}^k(x_i-D_{\tau+i-1})+\delta_{j,k}\mathcal I\Big)\Big]+c\Big(\mathbb E[I_{\tau+L}]-\mathcal I+L\,\mathbb E[D]-\sum_{i=1}^Lx_i\Big),
--   $$
--   where $I_{\tau+L}$ is the inventory at the end of the window started at $(\mathbf x,\mathcal I)$ and $\delta_{j,k}=1$ if $j=k$, $0$ otherwise.
--
--   This is the paper's Lemma 3: $\mathrm{windowCost}(\mathbf x,\mathcal I)$ is the conditional expectation $\mathbb E[\sum_{t=\tau}^{\tau+L-1}C^\pi_t\mid\mathbf x^\pi_\tau=\mathbf x,I^\pi_\tau=\mathcal I]$. It is the explicit form of the cost of any $L$ consecutive periods on which every later comparison rests.
--
--   **Formalization Note** The conditioning on $\{\mathbf x^\pi_\tau=\mathbf x, I^\pi_\tau=\mathcal I\}$ is rendered by starting the dynamics at $(\mathbf x,\mathcal I)$ (the demands of the window are independent of the state for every nonanticipative policy); the first conjunct states that this rendering integrates back to the policy's window cost. The window starts at Lean period $t_0$, the paper's $\tau=t_0+1$; it is stated for every $t_0$, which is the paper's range $\tau\in[1,T+1]$ for all horizons $T$. The right-hand side is a real number (the $c$-term is the expected lost demand) mapped into $[0,\infty]$ with `ENNReal.ofReal`; its expectations are Bochner integrals of bounded integrands.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 6, Lemma 3

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- Lemma 3, p. 6. First conjunct: for every admissible policy and every window start `t₀`
(the paper's `τ = t₀ + 1`), the expected cost of the `L` periods `t₀, …, t₀ + L − 1` is the
expectation of `windowCost` at the state `(x^π_τ, I^π_τ)`; this is how the conditional expectation
`E[· | x^π_τ = x, I^π_τ = 𝓘]` is rendered. Second conjunct: the formula of Lemma 3 for that
window cost started at pipeline `x` and inventory `𝓘` (`d (i − 1)` is `D_{τ+i−1}`, `slot x (i − 1)` is
`x_i`). -/
theorem lemma_3 (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P) :
    (∀ (π : CappedBaseStock.AdmissiblePolicy) (t₀ : ℕ),
      costWindow P prm π t₀ =
        ∫⁻ ω, windowCost P prm (CappedBaseStock.run prm π ω t₀).2
          (CappedBaseStock.run prm π ω t₀).1 ∂CappedBaseStock.sampleLaw P) ∧
    ∀ (x : Fin prm.L → ℝ≥0) (I : ℝ≥0),
      windowCost P prm x I =
        ENNReal.ofReal
          (prm.h * ∑ k ∈ Finset.Icc 1 prm.L,
              ∫ d, (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
                (fun j => (∑ i ∈ Finset.Icc (k + 1 - j) k,
                    ((slot x (i - 1) : ℝ) - (d (i - 1) : ℝ))) +
                  if j = k then (I : ℝ) else 0) ∂CappedBaseStock.demandPathLaw P +
            prm.p * ((∫ d, (endInventory prm x I d : ℝ) ∂CappedBaseStock.demandPathLaw P) -
              I + prm.L * CappedBaseStock.mean P - ∑ i, (x i : ℝ))) := by sorry

end LostSalesConstantOrder.LargeLeadTime
