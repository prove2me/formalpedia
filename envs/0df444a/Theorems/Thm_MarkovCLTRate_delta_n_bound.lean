-- Prove2me | Theorems.Thm_MarkovCLTRate_delta_n_bound
-- name    : MarkovCLTRate.delta_n_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:25.178258+00:00
-- url     : https://prove2.me/theorems/46165e77-41a1-4069-abf2-07a164561cc6
-- title:
--   The covariance-interaction term: $\Delta_n\le C(1-\beta)^{-2}n^{-\beta/2}$
-- statement:
--   In the setting of the proof of Theorem 3 with $\Sigma_\infty\succ0$, let $\beta\in(0,1)$ with $\beta\le p-2$. For the martingale increments $m_k$ of the chain, the covariance-interaction term of Theorem 1 satisfies
--   $$
--   \Delta_n\le\frac{C}{(1-\beta)^2}\,n^{-\beta/2}
--   $$
--   for all $n\ge n_0$, with $C$ and $n_0$ independent of $n$.
--
--   **Formalization Note** $\Delta_n$ takes values in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: a state space S (general) → [MeasurableSpace.CountablyGenerated S]; reason: Meyn and Tweedie's standing assumption; the paper borrows their machinery (p.17) and the proof rests on their Chapters 15-17
--   - generalization: p = 2 + β (item 1 of Theorem 3), repeated with p = 4 on p.22 (item 2) → one exponent 2 < p ≤ 4 in ProofSetting, with ‖g‖^p ≤ C_r𝒱 and ‖V_r‖ ≤ C(1 + 𝒱^{1/p}); reason: the same argument covers both; p = 2 + β and p = 4 are the two instances, so the statement specializes to the page's
--   - reading: the estimate inside the proof, where V_k^{−1/2} is used → for all n ≥ n₀ (∃ n₀ before n); reason: (14), which makes V_k invertible, holds only for all sufficiently large n (p.19); for small n, V_1 can be singular (paper.md R6: n = 1, d = 2, deterministic X_0)
--   - encoding: ∆_n, a real supremum over Lip_1 → deltaN valued in ℝ≥0∞; reason: a real ⨆ over the unbounded family Lip_1 would be the junk value 0; on finite values the two agree
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, proof of Theorem 3, p.22, bound on Δ_n

import Mathlib
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_MartingaleCLT
import Definitions.Def_MarkovCLTRate_GeneralChain
import Definitions.Def_MarkovCLTRate_ChainFunctionals

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **The covariance-interaction term**, arXiv:2401.15719v5, proof of Theorem 3, p.22. In the
setting of the proof with `Σ_∞ ≻ 0`, for `β ∈ (0, 1)` with `β ≤ p − 2`: after multiplying by the
global `n^{−1/2}` factor in Theorem 1,
`∆_n ≤ C/(1 − β)² n^{−β/2}`
for all sufficiently large `n`, where `∆_n` is the term of Theorem 1 for the martingale increments
`m_k` of the chain.

**Formalization Note.** `∆_n` is valued in `[0, ∞]` (a supremum over `Lip_1`). `C` and `n₀` are
chosen after `β`. -/
theorem delta_n_bound {S : Type*} [MeasurableSpace S]
    [MeasurableSpace.CountablyGenerated S] {d : ℕ}
    (P : Kernel S S) [IsMarkovKernel P] (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ)
    (r : S → Vec d) (p Cr : ℝ) (V : S → Vec d)
    (hset : ProofSetting P π η lyap lam L r p Cr V) (hSig : (sigmaInf P π V).PosDef)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hβp : β ≤ p - 2) :
    ∃ (C : ℝ) (n₀ : ℕ), ∀ n : ℕ, n₀ ≤ n →
      deltaN (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n
        ≤ ENNReal.ofReal (C / (1 - β) ^ 2 * (n : ℝ) ^ (-β / 2)) := by sorry

end MarkovCLTRate
