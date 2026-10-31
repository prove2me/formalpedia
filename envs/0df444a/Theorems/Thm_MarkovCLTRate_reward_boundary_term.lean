-- Prove2me | Theorems.Thm_MarkovCLTRate_reward_boundary_term
-- name    : MarkovCLTRate.reward_boundary_term
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:19.562738+00:00
-- url     : https://prove2.me/theorems/94202635-e73e-4f9b-ba02-8a797966e5a9
-- title:
--   Reward boundary term: $U_n=W_n+(V_r(X_0)-V_r(X_n))/\sqrt n$ and $d_{\mathcal W}(U_n,W_n)=O(n^{-1/2})$
-- statement:
--   In the setting of the proof of Theorem 3 (exponent $2<p\le4$, $V_r$ a solution of the Poisson equation with the growth bound (10)):
--
--   1. $\sup_{j\ge0}E\|V_r(X_j)\|<\infty$;
--   2. for every $n\ge1$ and every path,
--   $$
--   U_n=W_n+\frac{V_r(X_0)-V_r(X_n)}{\sqrt n},\qquad W_n=\frac1{\sqrt n}\sum_{k=1}^nm_k;
--   $$
--   3. there is $C$ with $d_{\mathcal W}(U_n,W_n)\le Cn^{-1/2}$ for all $n\ge1$.
--
--   This reduces the Markov chain CLT to the martingale CLT of Theorem 1 at the cost of $O(n^{-1/2})$.
--
--   **Formalization Note** Both laws are images of the chain's path law started from $\eta$.
--
--   Differences from the source:
--   - reading: a state space S (general) → [MeasurableSpace.CountablyGenerated S]; reason: Meyn and Tweedie's standing assumption; the paper borrows their machinery (p.17) and the proof rests on their Chapters 15-17
--   - generalization: p = 2 + β (item 1 of Theorem 3), repeated with p = 4 on p.22 (item 2) → one exponent 2 < p ≤ 4 in ProofSetting, with ‖g‖^p ≤ C_r𝒱 and ‖V_r‖ ≤ C(1 + 𝒱^{1/p}); reason: the same argument covers both; p = 2 + β and p = 4 are the two instances, so the statement specializes to the page's
--   - encoding: contributes only O(n^{−1/2}) in Wasserstein distance → ∃ C, ∀ n ≥ 1, d_W(law U_n, law W_n) ≤ C n^{−1/2}; reason: both laws have finite first moments, so one constant covers every n ≥ 1
--   - encoding: d_W(X, Y) = sup_{h ∈ Lip_1} E[h(X) − h(Y)], a real number → dW valued in ℝ≥0∞ (⊤ unless both laws are finite with finite first moments); reason: a real ⨆ over the unbounded family Lip_1 would be the junk value 0; every law compared here is a probability measure with a finite first moment, so the value is the page’s
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, proof of Theorem 3, p.19, boundary-term decomposition

import Mathlib
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_GeneralChain
import Definitions.Def_MarkovCLTRate_ChainFunctionals

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **The reward boundary term**, arXiv:2401.15719v5, proof of Theorem 3, p.19. In the setting of
the proof, (10) and (11) imply `sup_{j ≥ 0} E‖V_r(X_j)‖ < ∞`. Consequently
`U_n = W_n + (V_r(X_0) − V_r(X_n))/√n`, `W_n = (1/√n) Σ_{k=1}^n m_k`,
and the reward boundary term contributes only `O(n^{−1/2})` in Wasserstein distance:
`d_W(U_n, W_n) ≤ C n^{−1/2}` for all `n ≥ 1`.

**Formalization Note.** The decomposition holds for every path, since `V_r − PV_r = g` holds
pointwise. The `O(n^{−1/2})` is stated with one constant for all `n ≥ 1`. -/
theorem reward_boundary_term {S : Type*} [MeasurableSpace S]
    [MeasurableSpace.CountablyGenerated S] {d : ℕ}
    (P : Kernel S S) [IsMarkovKernel P] (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ)
    (r : S → Vec d) (p Cr : ℝ) (V : S → Vec d)
    (hset : ProofSetting P π η lyap lam L r p Cr V) :
    (⨆ j : ℕ, ∫⁻ ω, ‖V (ω j)‖ₑ ∂(MarkovChainCLT.chainMeasure P η) < ∞) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ ω : ℕ → S,
      Usum (centered π r) n ω = Wsum P V n ω + (Real.sqrt n)⁻¹ • (V (ω 0) - V (ω n))) ∧
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      dW ((MarkovChainCLT.chainMeasure P η).map (Usum (centered π r) n))
          ((MarkovChainCLT.chainMeasure P η).map (Wsum P V n))
        ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 : ℝ) / 2)) := by sorry

end MarkovCLTRate
