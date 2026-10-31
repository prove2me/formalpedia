-- Prove2me | Theorems.Thm_MarkovCLTRate_uniform_in_beta
-- name    : MarkovCLTRate.uniform_in_beta
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:16.337656+00:00
-- url     : https://prove2.me/theorems/9010e61e-2751-4ed1-b375-ca0de584de69
-- title:
--   Under $\|g\|^4\le C_r\mathcal V$: $d_{\mathcal W}(U_n,\Sigma_\infty^{1/2}Z)\le C(1-\beta)^{-2}n^{-\beta/2}$ with $C$ uniform in $\beta$
-- statement:
--   Assume the standing assumptions of Theorem 3, $\|g(x)\|^4\le C_r\mathcal V(x)$, a solution $V_r$ of the Poisson equation with $\|V_r(x)\|\le C(1+\mathcal V(x)^{1/4})$, and $\Sigma_\infty\succ0$. Then there is $C$ such that for every $\beta\in(0,1)$ and every $n\ge1$,
--   $$
--   d_{\mathcal W}\big(U_n,\Sigma_\infty^{1/2}Z\big)\le\frac{C}{(1-\beta)^2}\,n^{-\beta/2},\qquad Z\sim N(0,I).
--   $$
--   Choosing $\beta=1-2/\log n$ turns this into the $(\log n)^2/\sqrt n$ rate of item 2 of Theorem 3.
--
--   **Formalization Note** $C$ is chosen before $\beta$ and $n$. $\Sigma_\infty^{1/2}Z$ has law `multivariateGaussian 0 Σ∞`.
--
--   Differences from the source:
--   - reading: a state space S (general) → [MeasurableSpace.CountablyGenerated S]; reason: Meyn and Tweedie's standing assumption; the paper borrows their machinery (p.17) and the proof rests on their Chapters 15-17
--   - encoding: d_W(U_n, Σ∞^{1/2}Z) ≤ C/(1−β)² n^{−β/2} (for n where the argument applies) → ∀ n ≥ 1; reason: for each fixed n the distance is finite and the right side is at least C n^{−1/2}, so one constant covers every n ≥ 1 uniformly in β
--   - encoding: d_W(X, Y) = sup_{h ∈ Lip_1} E[h(X) − h(Y)], a real number → dW valued in ℝ≥0∞ (⊤ unless both laws are finite with finite first moments); reason: a real ⨆ over the unbounded family Lip_1 would be the junk value 0; every law compared here is a probability measure with a finite first moment, so the value is the page’s
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, proof of Theorem 3, p.22, second statement

import Mathlib
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_GeneralChain
import Definitions.Def_MarkovCLTRate_ChainFunctionals

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **Uniformity in `β` under the fourth-moment bound**, arXiv:2401.15719v5, proof of Theorem 3,
p.22. In the setting of the proof with `p = 4` (so `‖g‖⁴ ≤ C_r 𝒱` and `‖V_r‖ ≤ C(1 + 𝒱^{1/4})`)
and `Σ_∞ ≻ 0`, repeating the argument for any `β ∈ (0, 1)` gives
`d_W(U_n, Σ_∞^{1/2} Z) ≤ C/(1 − β)² n^{−β/2}`, with `C` uniform in `β`.

**Formalization Note.** `C` is chosen before `β` and `n`, and the bound is stated for all `n ≥ 1`.
`Σ_∞^{1/2} Z` has law `multivariateGaussian 0 Σ_∞`. -/
theorem uniform_in_beta {S : Type*} [MeasurableSpace S]
    [MeasurableSpace.CountablyGenerated S] {d : ℕ}
    (P : Kernel S S) [IsMarkovKernel P] (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ)
    (r : S → Vec d) (Cr : ℝ) (V : S → Vec d)
    (hset : ProofSetting P π η lyap lam L r 4 Cr V) (hSig : (sigmaInf P π V).PosDef) :
    ∃ C : ℝ, ∀ β : ℝ, 0 < β → β < 1 → ∀ n : ℕ, 1 ≤ n →
      dW ((MarkovChainCLT.chainMeasure P η).map (Usum (centered π r) n))
          (multivariateGaussian 0 (sigmaInf P π V))
        ≤ ENNReal.ofReal (C / (1 - β) ^ 2 * (n : ℝ) ^ (-β / 2)) := by sorry

end MarkovCLTRate
