-- Prove2me | Theorems.Thm_LooseHamHitting_Main_claim_8_2
-- name    : LooseHamHitting.Main.claim_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:19:49.015248+00:00
-- url     : https://prove2.me/theorems/6dc3dd5f-3078-4889-9575-e2ee10308dfa
-- title:
--   Claim 8.2 — stopped martingale estimate for log Φ(H_j) − L_j under P∗
-- statement:
--   In the setting of §8 (Assumption 4.2, the deletion laws $P$, $P_*$, $\beta$, $L_j$, the constant $C_0\ge1$ defining $\sigma^2$ and the stopping size $j_0$), for all sufficiently large $n_*$ and every $a>0$,
--   $$P_*\Big[\min_{j_0\le j\le\binom{n_*}3}\{\log\Phi(H_j)-L_j\}<-a-\sigma^2\Big]\le\beta^{-1}\exp\Big\{-\frac{a^2}{2\sigma^2}\Big\},$$
--   with $\log0=-\infty$ (a state with $\Phi(H_j)=0$ in the range is a failure). The Lean statement holds for every $C_0\ge1$, with the threshold on $n_*$ depending on $C_0$.
--
--   With $a=n_*/\log n_*$ and Lemma 7.3 this gives the counting lower bound up to the first failure of the marginal bound.
--
--   Differences from the source:
--   - generalization: C₀ fixed as in Proposition 8.1 → every C₀ ≥ 1; reason: the claim's proof uses only C₀ ≥ 1 and C₀(n∗ − s) ≤ m∗ (large n∗); it specializes to the constant of Proposition 8.1
--   - reading: "For sufficiently large n∗, Assumption 4.2 gives n∗ − s ≥ 2, m∗ < \binom{n∗}{3}, C₀(n∗ − s) ≤ m∗" (p. 31, just before the claim) → ∃ N (depending on C₀), the claim for n∗ ≥ N; reason: the claim is stated inside this standing context; for small n∗ the quantities (σ² = 0, Φ(\binom{[n∗]}{3}) = 0) are degenerate
--   - encoding: min over j₀ ≤ j ≤ \binom{n∗}{3} of log Φ(H_j) − L_j, log 0 = −∞ → ∃ j in the range with Φ(H_j) = 0 or log Φ(H_j) − L_j < −a − σ²; reason: finite minimum; the −∞ convention
--   - encoding: edge-deletion process, P∗ → uniform ordering of the triples, conditional counting probability; reason: same law
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 31, Claim 8.2

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Process
import Definitions.Def_LooseHamHitting_Main_Core

set_option autoImplicit false

open Classical

namespace LooseHamHitting.Main

/-- Claim 8.2: the stopped-martingale estimate for `log Φ(H_j) − L_j` under `P∗`, for every
`C₀ ≥ 1` (defining `j₀` and `σ²`) and all sufficiently large `n∗`. A state with `Φ(H_j) = 0`
counts as `log Φ(H_j) = −∞`. -/
theorem claim_8_2 :
    ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (m : ℕ) (ℓ : Fin n → ℕ) (M₀ : Finset (Finset (Fin n))), CoreAssumption n m ℓ M₀ →
      ∀ a : ℝ, 0 < a →
        condProbCore n m ℓ (fun σ => ∃ j : ℕ, stopSize C₀ n m M₀ σ ≤ j ∧ j ≤ n.choose 3 ∧
            (PhiCore n M₀ (prefixGraph σ j) = 0 ∨
              Real.log (PhiCore n M₀ (prefixGraph σ j)) - Lref n M₀ j <
                -a - sigmaSq C₀ n m M₀.card)) ≤
          (betaCore n m ℓ)⁻¹ * Real.exp (-(a ^ 2) / (2 * sigmaSq C₀ n m M₀.card)) := by sorry

end LooseHamHitting.Main
