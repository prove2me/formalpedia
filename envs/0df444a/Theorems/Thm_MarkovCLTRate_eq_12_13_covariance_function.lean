-- Prove2me | Theorems.Thm_MarkovCLTRate_eq_12_13_covariance_function
-- name    : MarkovCLTRate.eq_12_13_covariance_function
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:48.013996+00:00
-- url     : https://prove2.me/theorems/29a0152d-fdd0-4cac-aa98-f9e52495537f
-- title:
--   (12)–(13): the conditional covariance function and $\|E(\Sigma_k)-\Sigma_\infty\|_{op}\le C\rho^k$
-- statement:
--   In the setting of the proof of Theorem 3 (exponent $2<p\le4$, $b=2/p$), with $v(x)=E[m_1m_1^\top\mid X_0=x]$:
--
--   1. $\Sigma_k=E(m_km_k^\top\mid\mathcal F_{k-1})=v(X_{k-1})$ almost surely, for every $k\ge1$;
--   2. $\|v(x)\|_{op}\le C\big(1+\mathcal V(x)^b\big)$ for all $x$; $\quad(12)$
--   3. $\Sigma_\infty=\pi v$, which is finite;
--   4. there are $C$ and $\rho\in(0,1)$ with $\|E(\Sigma_k)-\Sigma_\infty\|_{op}\le C\rho^k$ for all $k\ge1$. $\quad(13)$
--
--   The chain starts from $\eta$, so $E(\Sigma_k)$ depends on $k$; (13) says it converges geometrically to the stationary covariance $\Sigma_\infty$.
--
--   **Formalization Note** $\pi v$ is the entrywise $\pi$-integral of $v$; $\mathcal F_k=\sigma(X_0,\dots,X_k)$.
--
--   Differences from the source:
--   - reading: a state space S (general) → [MeasurableSpace.CountablyGenerated S]; reason: Meyn and Tweedie's standing assumption; the paper borrows their machinery (p.17) and the proof rests on their Chapters 15-17
--   - generalization: p = 2 + β (item 1 of Theorem 3), repeated with p = 4 on p.22 (item 2) → one exponent 2 < p ≤ 4 in ProofSetting, with ‖g‖^p ≤ C_r𝒱 and ‖V_r‖ ≤ C(1 + 𝒱^{1/p}); reason: the same argument covers both; p = 2 + β and p = 4 are the two instances, so the statement specializes to the page's
--   - encoding: Σ_k = v(X_{k−1}) → condCov … k =ᵐ fun ω => vCov (ω (k−1)); reason: Σ_k is a conditional expectation, defined up to null sets
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, proof of Theorem 3, p.19, v, Σ_k = v(X_{k−1}), (12), Σ∞ = πv, (13)

import Mathlib
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_MartingaleCLT
import Definitions.Def_MarkovCLTRate_GeneralChain
import Definitions.Def_MarkovCLTRate_ChainFunctionals

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **The conditional covariance function, (12) and (13)**, arXiv:2401.15719v5, proof of
Theorem 3, p.19. In the setting of the proof (`2 < p ≤ 4`, `a = 1/p`, `b = 2/p`), with
`v(x) = E[m_1 m_1ᵀ | X_0 = x]`:
1. `Σ_k = E(m_k m_kᵀ | 𝓕_{k−1}) = v(X_{k−1})` almost surely, for every `k ≥ 1`;
2. `‖v(x)‖_op ≤ C(1 + 𝒱(x)^b)`   (12);
3. `Σ_∞ = πv`, which is finite;
4. `‖E(Σ_k) − Σ_∞‖_op ≤ C ρ^k` for some `ρ ∈ (0, 1)` and all `k ≥ 1`   (13).

**Formalization Note.** `𝓕_k = σ(X_0, …, X_k)` and the chain starts from `η`. `πv` is the entrywise
`π`-integral of `v`. -/
theorem eq_12_13_covariance_function {S : Type*} [MeasurableSpace S]
    [MeasurableSpace.CountablyGenerated S] {d : ℕ}
    (P : Kernel S S) [IsMarkovKernel P] (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ)
    (r : S → Vec d) (p Cr : ℝ) (V : S → Vec d)
    (hset : ProofSetting P π η lyap lam L r p Cr V) :
    (∀ k : ℕ, 1 ≤ k →
      condCov (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) k
        =ᵐ[MarkovChainCLT.chainMeasure P η] fun ω => vCov P V (ω (k - 1))) ∧
    (∃ C : ℝ, ∀ x : S, opNorm (vCov P V x) ≤ C * (1 + lyap x ^ (2 / p))) ∧
    sigmaInf P π V = Matrix.of (fun i j => ∫ x, vCov P V x i j ∂π) ∧
    ∃ C ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ k : ℕ, 1 ≤ k →
      opNorm (expCov (MarkovChainCLT.chainMeasure P η) (pathFiltration S) (mChain P V) k
          - sigmaInf P π V) ≤ C * ρ ^ k := by sorry

end MarkovCLTRate
