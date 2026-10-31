-- Prove2me | Theorems.Thm_MarkovCLTRate_eq_11_uniform_moments
-- name    : MarkovCLTRate.eq_11_uniform_moments
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:10.364778+00:00
-- url     : https://prove2.me/theorems/1a35b8f3-2a58-49aa-9abf-290d6cc63fd9
-- title:
--   (11): uniform Lyapunov moments and uniform $p$th moments of $m_k$
-- statement:
--   Under the standing assumptions of Theorem 3,
--   $$
--   \sup_{j\ge0}E[\mathcal V(X_j)]<\infty.\qquad(11)
--   $$
--   In the setting of the proof (exponent $2<p\le4$, $V_r$ a solution of the Poisson equation with $\|V_r\|\le C(1+\mathcal V^{1/p})$), the martingale increments $m_k=V_r(X_k)-E[V_r(X_k)\mid X_{k-1}]$ have uniformly bounded $p$th moments:
--   $$
--   \sup_{k\ge1}E\|m_k\|^p<\infty .
--   $$
--   Both bounds hold for the chain started from its initial distribution $\eta$.
--
--   **Formalization Note** The expectations are lower Lebesgue integrals under the path law, so neither bound is vacuous.
--
--   Differences from the source:
--   - reading: a state space S (general) → [MeasurableSpace.CountablyGenerated S]; reason: Meyn and Tweedie's standing assumption; the paper borrows their machinery (p.17) and the proof rests on their Chapters 15-17
--   - generalization: p = 2 + β (item 1 of Theorem 3), repeated with p = 4 on p.22 (item 2) → one exponent 2 < p ≤ 4 in ProofSetting, with ‖g‖^p ≤ C_r𝒱 and ‖V_r‖ ≤ C(1 + 𝒱^{1/p}); reason: the same argument covers both; p = 2 + β and p = 4 are the two instances, so the statement specializes to the page's
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, proof of Theorem 3, p.18, (11) and the moment bound after it

import Mathlib
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_GeneralChain
import Definitions.Def_MarkovCLTRate_ChainFunctionals

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **(11) and the uniform `p`th moments of `m_k`**, arXiv:2401.15719v5, proof of Theorem 3, p.18.
Under the assumptions of Theorem 3, the drift condition gives
`sup_{j ≥ 0} E[𝒱(X_j)] < ∞`   (11),
and in the setting of the proof (`2 < p ≤ 4`, `V_r` a solution of the Poisson equation with the
growth bound (10), `a = 1/p`) the martingale increments
`m_k = V_r(X_k) − E[V_r(X_k) | X_{k−1}]` have uniformly bounded `p`th moments:
`sup_{k ≥ 1} E‖m_k‖^p < ∞`.

**Formalization Note.** The chain starts from `η` and the expectations are lower Lebesgue
integrals under the path law, so neither bound is vacuous. -/
theorem eq_11_uniform_moments {S : Type*} [MeasurableSpace S]
    [MeasurableSpace.CountablyGenerated S] {d : ℕ}
    (P : Kernel S S) [IsMarkovKernel P] (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ) :
    (GeoDriftChain P π η lyap lam L →
      ⨆ j : ℕ, ∫⁻ ω, ENNReal.ofReal (lyap (ω j)) ∂(MarkovChainCLT.chainMeasure P η) < ∞) ∧
    (∀ (r : S → Vec d) (p Cr : ℝ) (V : S → Vec d), ProofSetting P π η lyap lam L r p Cr V →
      ⨆ k : ℕ, ⨆ (_ : 1 ≤ k),
        ∫⁻ ω, ‖mChain P V k ω‖ₑ ^ p ∂(MarkovChainCLT.chainMeasure P η) < ∞) := by sorry

end MarkovCLTRate
