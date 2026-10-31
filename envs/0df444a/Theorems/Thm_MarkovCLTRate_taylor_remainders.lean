-- Prove2me | Theorems.Thm_MarkovCLTRate_taylor_remainders
-- name    : MarkovCLTRate.taylor_remainders
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:29.180923+00:00
-- url     : https://prove2.me/theorems/f3e3f751-ff13-4de9-bbd7-54def9817f92
-- title:
--   Taylor remainders of Theorem 1 for the chain: $\le C(1-\beta)^{-2}n^{-\beta/2}$
-- statement:
--   1. There is an absolute constant $C$ with
--   $$
--   \sum_{q=1}^nq^{-(1+\beta)/2}\le\frac{C}{1-\beta}\,n^{(1-\beta)/2}\qquad\text{for all }\beta\in(0,1),\ n\ge1 .
--   $$
--   2. In the setting of the proof of Theorem 3 with $\Sigma_\infty\succ0$, for every $\beta\in(0,1)$ with $\beta\le p-2$ there are $C$ and $n_0$ such that, for all $n\ge n_0$, the sum of the two Taylor remainders of Theorem 1 for the increments $m_k$,
--   $$
--   \frac1{\sqrt n}\sum_{k=1}^n\Big[\tilde C_1\|V_k^{1/2}\|_{op}E\|V_k^{-1/2}m_k\|^{2+\beta}+\tilde C_1\operatorname{Tr}(D_k)\|V_k^{1/2}\|_{op}E\|V_k^{-1/2}m_k\|^{\beta}\Big],
--   $$
--   is at most $\frac{C}{(1-\beta)^2}n^{-\beta/2}$.
--
--   **Formalization Note** $p=2+\beta$ in item 1 of Theorem 3, and $p=4$ with any $\beta\in(0,1)$ in item 2 (p.22).
--
--   Differences from the source:
--   - reading: a state space S (general) → [MeasurableSpace.CountablyGenerated S]; reason: Meyn and Tweedie's standing assumption; the paper borrows their machinery (p.17) and the proof rests on their Chapters 15-17
--   - generalization: p = 2 + β (item 1 of Theorem 3), repeated with p = 4 on p.22 (item 2) → one exponent 2 < p ≤ 4 in ProofSetting, with ‖g‖^p ≤ C_r𝒱 and ‖V_r‖ ≤ C(1 + 𝒱^{1/p}); reason: the same argument covers both; p = 2 + β and p = 4 are the two instances, so the statement specializes to the page's
--   - reading: the estimate inside the proof, where V_k^{−1/2} is used → for all n ≥ n₀ (∃ n₀ before n); reason: (14), which makes V_k invertible, holds only for all sufficiently large n (p.19); for small n, V_1 can be singular (paper.md R6: n = 1, d = 2, deterministic X_0)
--   - encoding: both Taylor remainders are bounded by a constant times (1/√n)(1/(1−β)) Σ q_k^{−(1+β)/2} ≤ C/(1−β)² n^{−β/2} → the sum of the two remainders (taylorBound) ≤ C/(1−β)² n^{−β/2}, plus the elementary sum bound as a separate clause; reason: the intermediate 'constant times' expression is the proof's route; the conclusion and the sum bound are what the page states
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, proof of Theorem 3, p.20, Taylor remainders

import Mathlib
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_MartingaleCLT
import Definitions.Def_MarkovCLTRate_GeneralChain
import Definitions.Def_MarkovCLTRate_ChainFunctionals

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **The Taylor remainders**, arXiv:2401.15719v5, proof of Theorem 3, p.20. In the setting of the
proof with `Σ_∞ ≻ 0`, for `β ∈ (0, 1)` with `β ≤ p − 2`: since `C̃₁(d, β) ≤ C/(1 − β)`, both Taylor
remainders in Theorem 1 are bounded by a constant times
`(1/√n) (1/(1 − β)) Σ_{k=1}^n q_k^{−(1+β)/2} ≤ C/(1 − β)² n^{−β/2}`, where
`Σ_{q=1}^n q^{−(1+β)/2} ≤ C/(1 − β) n^{(1−β)/2}`.

Stated as: (i) there is an absolute constant `C` with
`Σ_{q=1}^n q^{−(1+β)/2} ≤ C/(1 − β) n^{(1−β)/2}` for all `β ∈ (0, 1)` and `n ≥ 1`; (ii) for the
martingale increments `m_k` of the chain there are `C` and `n₀` such that, for every `n ≥ n₀`, the
Taylor-remainder part of the bound of Theorem 1 is at most `C/(1 − β)² n^{−β/2}`.

**Formalization Note.** `n ≥ n₀` is the range in which (14) holds and the `V_k` are invertible.
`p = 2 + β` in item 1 of Theorem 3; `p = 4` with any `β ∈ (0, 1)` in item 2 (p.22). -/
theorem taylor_remainders {S : Type*} [MeasurableSpace S]
    [MeasurableSpace.CountablyGenerated S] {d : ℕ}
    (P : Kernel S S) [IsMarkovKernel P] (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ)
    (r : S → Vec d) (p Cr : ℝ) (V : S → Vec d)
    (hset : ProofSetting P π η lyap lam L r p Cr V) (hSig : (sigmaInf P π V).PosDef) :
    (∃ C : ℝ, ∀ β : ℝ, 0 < β → β < 1 → ∀ n : ℕ, 1 ≤ n →
      ∑ q ∈ Finset.Icc 1 n, (q : ℝ) ^ (-(1 + β) / 2) ≤ C / (1 - β) * (n : ℝ) ^ ((1 - β) / 2)) ∧
    ∀ β : ℝ, 0 < β → β < 1 → β ≤ p - 2 →
      ∃ (C : ℝ) (n₀ : ℕ), ∀ n : ℕ, n₀ ≤ n →
        taylorBound (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n β
          ≤ C / (1 - β) ^ 2 * (n : ℝ) ^ (-β / 2) := by sorry

end MarkovCLTRate
