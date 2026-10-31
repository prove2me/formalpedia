-- Prove2me | Theorems.Thm_MarkovCLTRate_theorem_3_general_state_clt_rate
-- name    : MarkovCLTRate.theorem_3_general_state_clt_rate
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:10.299587+00:00
-- url     : https://prove2.me/theorems/15df7423-30e4-43d4-95ab-c8f9122182eb
-- title:
--   Theorem 3: $d_{\mathcal W}(U_n,\Sigma_\infty^{1/2}Z)\le C(1-\beta)^{-2}n^{-\beta/2}$, and $O((\log n)^2/\sqrt n)$ under a fourth-moment bound, for general state-space chains
-- statement:
--   Let $X$ be a $\psi$-irreducible, aperiodic Markov chain on a state space $\mathcal S$, with transition kernel $P$ and invariant distribution $\pi$. Suppose there is a Lyapunov function $\mathcal V\ge1$, unbounded off petite sets, with $E[\mathcal V(X_0)]<\infty$ and
--   $$
--   P\mathcal V(x)=E[\mathcal V(X_{k+1})\mid X_k=x]\le\lambda\mathcal V(x)+L\qquad(8)
--   $$
--   for some $\lambda\in[0,1)$ and $L<\infty$. Let $r:\mathcal S\to\Re^d$ satisfy $\pi\|r\|<\infty$, let $\bar r=\pi r$ and define
--   $$
--   g=r-\bar r,\qquad U_n=\frac1{\sqrt n}\sum_{k=1}^ng(X_{k-1}).
--   $$
--   Then:
--
--   1. Fix $\beta\in(0,1)$. If $\|g(x)\|^{2+\beta}\le C_r\mathcal V(x)$ for all $x$ and some $C_r<\infty$, the Poisson equation $V_r-PV_r=g$ has a solution with $\|V_r(x)\|\le C(1+\mathcal V(x)^{1/(2+\beta)})$. For such a solution let $m_k=V_r(X_k)-E[V_r(X_k)\mid X_{k-1}]$ and $\Sigma_\infty=E_\pi[m_1m_1^\top]$. If $\Sigma_\infty\succ0$, then for all $n\ge1$
--   $$
--   d_{\mathcal W}\big(U_n,\Sigma_\infty^{1/2}Z\big)\le\frac{C}{(1-\beta)^2}\,n^{-\beta/2},\qquad Z\sim N(0,I),
--   $$
--   where $C$ does not depend on $n$.
--   2. If $\|g(x)\|^4\le C_r\mathcal V(x)$ for all $x$, the Poisson equation has a solution with $\|V_r(x)\|\le C(1+\mathcal V(x)^{1/4})$; for such a solution, if $\Sigma_\infty\succ0$, then
--   $$
--   d_{\mathcal W}\big(U_n,\Sigma_\infty^{1/2}Z\big)=O\Big(\frac{(\log n)^2}{\sqrt n}\Big).
--   $$
--
--   The initial distribution is arbitrary subject to $E[\mathcal V(X_0)]<\infty$. This is a nonasymptotic, multivariate central limit theorem for additive functionals of general state-space Markov chains under geometric drift; with $\mathcal V\equiv1$ it covers finite aperiodic chains.
--
--   **Formalization Note** The law of $U_n$ is the image of the chain's path law started from $\eta$, and $\Sigma_\infty^{1/2}Z$ has law `multivariateGaussian 0 Σ∞`. The terms $\psi$-irreducible, aperiodic, petite and unbounded off petite sets are defined in `MarkovCLTRate.GeneralChain`.
--
--   Differences from the source:
--   - reading: the Poisson equation has a solution "with the growth bound used below" (item 1); "define V_r … as above" (item 2) → ∃ V_r Poisson solution with ‖V_r‖ ≤ C(1 + 𝒱^{1/(2+β)}) in item 1 and ‖V_r‖ ≤ C(1 + 𝒱^{1/4}) in item 2; reason: the bound used below is (10), p.18, with a = 1/(2+β); p.22 fixes the exponent 1/4 for the second statement
--   - reading: a solution V_r, then m_k and Σ∞ defined from it → the rate for every Poisson solution with that growth bound; reason: two such solutions differ by h with h = Ph and growth 𝒱^a, so h is constant by (9); m_k and Σ∞ are then the same, and the ∀ form avoids a hidden choice
--   - reading: a state space S (general) → [MeasurableSpace.CountablyGenerated S]; reason: Meyn and Tweedie's standing assumption; the paper borrows their machinery (p.17) and the proof rests on their Chapters 15-17
--   - encoding: ψ-irreducible, aperiodic, petite, unbounded off petite sets (Meyn–Tweedie terms, not defined in the paper) → PsiIrreducible, Aperiodic, IsPetite, UnboundedOffPetite of MarkovCLTRate.GeneralChain; reason: written from Meyn and Tweedie's definitions, with nonzero measures where they ask for a measure
--   - encoding: 𝒱 ≥ 1, E[𝒱(X_0)] < ∞ and P𝒱(x) ≤ λ𝒱(x) + L → measurable real 𝒱 with lower Lebesgue integrals for P𝒱 and E𝒱(X_0); r measurable; reason: the expectations are those of nonnegative functions; measurability is implicit in them
--   - encoding: d_W(U_n, Σ∞^{1/2}Z), Z ∼ N(0, I) → dW (law of U_n under chainMeasure P η) (multivariateGaussian 0 Σ∞), valued in [0, ∞]; reason: Σ∞^{1/2}Z has that law; d_W depends only on the laws
--   - encoding: C does not depend on n (item 1) → ∃ C after all data including β and V_r, then ∀ n ≥ 1; reason: U_n needs n ≥ 1; C may depend on β (unlike Theorem 2, the page only says it does not depend on n)
--   - encoding: = O((log n)²/√n) (item 2) → ∃ C N, ∀ n ≥ N, d_W ≤ C (log n)²/√n; reason: O(·) as n → ∞; at n = 1, log n = 0, so the bound cannot be required for every n ≥ 1
--   - encoding: the Poisson equation V_r − PV_r = g has a solution → IsPoissonSolution, i.e. V_r measurable, integrable against every P(x, ·), and V_r(x) − PV_r(x) = g(x) for every x; reason: PV_r(x) is defined only for such V_r; the Meyn–Tweedie solution is one
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, Theorem 3, pp.17–18 (items 1 and 2; growth bounds (10), p.18, and p.22)

import Mathlib
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_GeneralChain
import Definitions.Def_MarkovCLTRate_ChainFunctionals

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace MarkovCLTRate

/-- **Theorem 3** of Srikant, *Rates of Convergence in the Central Limit Theorem for Markov Chains,
with an Application to TD Learning*, arXiv:2401.15719v5, pp.17–18.

Let `X` be a `ψ`-irreducible, aperiodic Markov chain on `S` with transition kernel `P`, invariant
distribution `π` and initial distribution `η`, with a Lyapunov function `𝒱 ≥ 1` unbounded off
petite sets, `E[𝒱(X_0)] < ∞` and `P𝒱 ≤ λ𝒱 + L` (8). Let `r : S → ℜ^d` with `π‖r‖ < ∞`,
`g = r − πr`, `U_n = n^{−1/2} Σ_{k=1}^n g(X_{k−1})`.
1. For `β ∈ (0, 1)` and `‖g‖^{2+β} ≤ C_r 𝒱`: the Poisson equation `V_r − PV_r = g` has a solution
   with the growth bound `‖V_r‖ ≤ C(1 + 𝒱^{1/(2+β)})` of (10); and for such a solution, if
   `Σ_∞ = E_π[m_1 m_1ᵀ] ≻ 0`, then `d_W(U_n, Σ_∞^{1/2} Z) ≤ C (1 − β)^{−2} n^{−β/2}` with `C`
   independent of `n`.
2. For `‖g‖^4 ≤ C_r 𝒱`: a solution with `‖V_r‖ ≤ C(1 + 𝒱^{1/4})` (p.22) exists, and for such a
   solution with `Σ_∞ ≻ 0`, `d_W(U_n, Σ_∞^{1/2} Z) = O((log n)²/√n)`.

**Formalization Note.** `S` has a countably generated σ-algebra, Meyn–Tweedie's standing
assumption (the paper borrows their machinery, p.17). The law of `U_n` is the image of the chain's
path law; `Σ_∞^{1/2} Z` has law `multivariateGaussian 0 Σ_∞`. The rate is stated for every
solution `V_r` with the growth bound (any two differ by a constant, so `m_k` and `Σ_∞` do not
depend on the choice). `C` may depend on everything except `n`; in item 2 the bound holds for
`n ≥ N` because `log 1 = 0`. -/
theorem theorem_3_general_state_clt_rate {S : Type*} [MeasurableSpace S]
    [MeasurableSpace.CountablyGenerated S] {d : ℕ}
    (P : Kernel S S) [IsMarkovKernel P] (π η : Measure S) (lyap : S → ℝ) (lam L : ℝ)
    (hchain : GeoDriftChain P π η lyap lam L)
    (r : S → Vec d) (hr : Measurable r) (hrπ : Integrable r π) :
    (∀ β : ℝ, 0 < β → β < 1 → ∀ Cr : ℝ, (∀ x, ‖centered π r x‖ ^ (2 + β) ≤ Cr * lyap x) →
      (∃ V : S → Vec d, IsPoissonSolution P (centered π r) V ∧
          GrowthBound lyap (1 / (2 + β)) V) ∧
      ∀ V : S → Vec d, IsPoissonSolution P (centered π r) V →
        GrowthBound lyap (1 / (2 + β)) V → (sigmaInf P π V).PosDef →
        ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
          dW ((MarkovChainCLT.chainMeasure P η).map (Usum (centered π r) n))
              (multivariateGaussian 0 (sigmaInf P π V))
            ≤ ENNReal.ofReal (C / (1 - β) ^ 2 * (n : ℝ) ^ (-β / 2))) ∧
    (∀ Cr : ℝ, (∀ x, ‖centered π r x‖ ^ (4 : ℝ) ≤ Cr * lyap x) →
      (∃ V : S → Vec d, IsPoissonSolution P (centered π r) V ∧
          GrowthBound lyap (1 / 4) V) ∧
      ∀ V : S → Vec d, IsPoissonSolution P (centered π r) V →
        GrowthBound lyap (1 / 4) V → (sigmaInf P π V).PosDef →
        ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          dW ((MarkovChainCLT.chainMeasure P η).map (Usum (centered π r) n))
              (multivariateGaussian 0 (sigmaInf P π V))
            ≤ ENNReal.ofReal (C * Real.log n ^ 2 / Real.sqrt n)) := by sorry

end MarkovCLTRate
