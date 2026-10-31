-- Prove2me | Theorems.Thm_MarkovCLTRate_weighted_comparison
-- name    : MarkovCLTRate.weighted_comparison
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:20.162315+00:00
-- url     : https://prove2.me/theorems/5c782a04-06f2-4ca0-a729-f851c9116892
-- title:
--   Weighted three-part comparison: $\sum_k E[\|H_k-H_{k-1}\|_{op}(1+\mathcal V(X_{k-1})^b)]\le C(1-\beta)^{-2}n^{(1-\beta)/2}$
-- statement:
--   In the setting of the proof of Theorem 3 with $\Sigma_\infty\succ0$ and $b=2/p$, let $\beta\in(0,1)$ with $\beta\le p-2$. There are $C$ and $n_0$ such that for all $n\ge n_0$ and all $h\in Lip_1$,
--   $$
--   \sum_{k=2}^nE\Big[\|H_k-H_{k-1}\|_{op}\big(1+\mathcal V(X_{k-1})^b\big)\Big]\le\frac{C}{(1-\beta)^2}\,n^{(1-\beta)/2}.
--   $$
--   This weighted version of Lemma 3 controls the last sum in (19).
--
--   **Formalization Note** The expectations are lower Lebesgue integrals. $C$ and $n_0$ may depend on $\beta$ and are chosen before $n$ and $h$.
--
--   Differences from the source:
--   - reading: a state space S (general) → [MeasurableSpace.CountablyGenerated S]; reason: Meyn and Tweedie's standing assumption; the paper borrows their machinery (p.17) and the proof rests on their Chapters 15-17
--   - generalization: p = 2 + β (item 1 of Theorem 3), repeated with p = 4 on p.22 (item 2) → one exponent 2 < p ≤ 4 in ProofSetting, with ‖g‖^p ≤ C_r𝒱 and ‖V_r‖ ≤ C(1 + 𝒱^{1/p}); reason: the same argument covers both; p = 2 + β and p = 4 are the two instances, so the statement specializes to the page's
--   - reading: the estimate inside the proof, where V_k^{−1/2} is used → for all n ≥ n₀ (∃ n₀ before n); reason: (14), which makes V_k invertible, holds only for all sufficiently large n (p.19); for small n, V_1 can be singular (paper.md R6: n = 1, d = 2, deterministic X_0)
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, proof of Theorem 3, p.21, three-part comparison (last display)

import Mathlib
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_MartingaleCLT
import Definitions.Def_MarkovCLTRate_GeneralChain
import Definitions.Def_MarkovCLTRate_ChainFunctionals

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **The weighted three-part comparison**, arXiv:2401.15719v5, proof of Theorem 3, p.21. In the
setting of the proof with `Σ_∞ ≻ 0` and `b = 2/p`, for `β ∈ (0, 1)` with `β ≤ p − 2` (so that
Hölder's inequality applies with `p − β ≥ 2`), the spatial-shift, internal-covariance and
external-covariance estimates give
`Σ_{k=2}^n E[‖H_k − H_{k−1}‖_op (1 + 𝒱(X_{k−1})^b)]
  ≤ C Σ_{q=1}^{n−1} q^{−3/2} + C/(1 − β) Σ_{q=1}^{n−1} q^{−(1+β)/2} ≤ C/(1 − β)² n^{(1−β)/2}`,
uniformly over `h ∈ Lip_1`.

**Formalization Note.** Stated for all sufficiently large `n` (where (14) holds), with `C` and `n₀`
chosen before `n` and `h`. The expectations are lower Lebesgue integrals, so the bound cannot hold
by a non-integrable integrand defaulting to `0`. -/
theorem weighted_comparison {S : Type*} [MeasurableSpace S]
    [MeasurableSpace.CountablyGenerated S] {d : ℕ}
    (P : Kernel S S) [IsMarkovKernel P] (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ)
    (r : S → Vec d) (p Cr : ℝ) (V : S → Vec d)
    (hset : ProofSetting P π η lyap lam L r p Cr V) (hSig : (sigmaInf P π V).PosDef)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hβp : β ≤ p - 2) :
    ∃ (C : ℝ) (n₀ : ℕ), ∀ n : ℕ, n₀ ≤ n → ∀ h : Vec d → ℝ, LipschitzWith 1 h →
      ∑ k ∈ Finset.Icc 2 n, ∫⁻ ω, ENNReal.ofReal
          (opNorm (Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n k h ω
              - Hmat (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) n (k - 1)
                  h ω)
            * (1 + lyap (ω (k - 1)) ^ (2 / p))) ∂(MarkovChainCLT.chainMeasure P η)
        ≤ ENNReal.ofReal (C / (1 - β) ^ 2 * (n : ℝ) ^ ((1 - β) / 2)) := by sorry

end MarkovCLTRate
