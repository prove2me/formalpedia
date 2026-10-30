-- Prove2me | Theorems.Thm_GarberOLO_Alg3_dist_recursion
-- name    : GarberOLO.Alg3.dist_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:04:00.799396+00:00
-- url     : https://prove2.me/theorems/a958776c-4364-4b46-aa53-ea1505e0fc81
-- title:
--   Per-round distance recursion (proof of Theorem 1, p. 15)
-- statement:
--   Throughout, $K, \mathcal F \subset \mathbb R^d_+$ are compact, $\|x\| \le R$ on $K$, $\|f\| \le F$ on $\mathcal F$, $0 \le x\cdot f \le C$ on $K \times \mathcal F$ ($R, F, C > 0$), and $\mathcal O_K$ is an $\alpha$-approximate linear optimization oracle for $K$ ($\alpha > 0$; §2.1).
--
--   Let $c > 0$ be the constant of the prescribed $N$, $s_1 \in K$, $\eta > 0$, $\varepsilon \in (0, (\alpha+2)R]$, $T \ge 1$ and $f_1, \dots, f_T \in \mathcal F$, and run Algorithm 3 with an optimal solution of Problem (5) in every call of Algorithm 2. For every round $t \in \{1, \dots, T\}$, with $k_t$ the number of passes of the loop of the round-$t$ call of Algorithm 2 and $\mathrm{dist}$ the distance to $\mathrm{CH}(\alpha K)$,
--   $$\mathrm{dist}^2(\tilde y_{t+1}) \le \mathrm{dist}^2(\tilde y_t) + 2\eta F\, \mathrm{dist}(\tilde y_t) + \eta^2F^2 - k_t\varepsilon^2 + \varepsilon^2 .$$
--   This holds for $\alpha \ge 1$ ($y_{t+1} = \tilde y_t - \eta f_t$) and for $\alpha < 1$ ($y_{t+1} = \tilde y_t + \eta f_t$).
--
--   Summed over the rounds, this recursion bounds the total number of passes $\sum_t k_t$ and hence the average oracle complexity in Theorem 1.
--
--   Differences from the source:
--   - generalization: c the paper's fixed universal constant → every c > 0; reason: the recursion uses only termination and the decrease clause of Lemma 7, which hold for every N ≥ 1, so it holds for every positive c and in particular for the paper's
--   - generalization: the display is written for α ≥ 1 (y_{t+1} = ỹ_t − ηf_t; "the proof for the complementary follows … up to changes in the obvious places") → both α ≥ 1 and α < 1 (y_{t+1} = ỹ_t + ηf_t); reason: the α < 1 case is the paper's "obvious changes" and contains the printed case
--   - reading: the chain of the display → its two endpoints only; reason: the intermediate lines are steps of the proof
--   - reading: "the Ellipsoid method" (Lemma 5, p. 9), not specified further → the central-cut Ellipsoid method from E₀ = B(0,1) (ellipsoidCut, sdState), with bisection for d = 1 and no change on a zero cut vector; reason: E₀ = B(0,1) is the ball of Problem (4)'s constraint, which the proof on p. 11 needs (B(h/2, r) ⊂ B(0,1)); the standard update divides by d² − 1 = 0 when d = 1; a zero cut arises only when v = x, and then p = x (paper.md Reading 1)
--   - reading: N "as prescribed in Lemma 5" (Algorithm 2, line 8), any positive integer N ≥ c d² ln(((α+1)R + ‖x‖)/ε) → N = Nprescribed S c ε ỹ = max{1, ⌈c d² ln(((α+1)R + ‖ỹ‖)/ε)⌉}, recomputed at the current ỹ of each loop pass; reason: with N unbounded the oracle-call count is unbounded, so the least admissible N is the only reading under which the call bounds can hold (paper.md Reading 2)
--   - reading: "an optimal solution" of Problem (5), "some point" s₁ ∈ K, and the oracle O_K → arbitrary: every selector sel with IsOptimalSelector sel, every s₁ ∈ K, every OK with IsApproxOracle S OK; reason: the paper leaves these choices free and claims the result for every choice (paper.md Reading 5)
--   - encoding: dist(x, CH(αK)) = min_{z∈CH(αK)} ‖z − x‖ (§2.2) → Metric.infDist x (convexHull ℝ (α • K)); reason: CH(αK) is nonempty (an oracle value lies in K) and compact, so the infimum is the attained minimum
--   - encoding: "T rounds" (and division by T) → 1 ≤ T; reason: T rounds with a division by T presuppose T ≥ 1 (paper.md item 11)
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, proof of Theorem 1, p. 15 (unnumbered display)

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_IsApproxOracle
import Definitions.Def_GarberOLO_Alg3_IsOptimalSelector
import Definitions.Def_GarberOLO_Alg3_alg3Y
import Definitions.Def_GarberOLO_Alg3_alg3Call

open scoped Pointwise

namespace GarberOLO.Alg3

/-- **The per-round distance recursion** (proof of Theorem 1, p. 15, unnumbered display).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, proof of Theorem 1, p. 15: "By Lemma 7, it follows that on any iteration t,
dist²(ỹ_{t+1}, CH(αK)) ≤ dist²(y_{t+1}, CH(αK)) − (k_t − 1)ε² = dist²(ỹ_t − ηf_t, CH(αK)) −
(k_t − 1)ε² ≤ (dist(ỹ_t, CH(αK)) + ηF)² − (k_t − 1)ε² = dist²(ỹ_t, CH(αK)) + 2ηF dist(ỹ_t, CH(αK))
+ η²F² − k_tε² + ε²."

For every positive constant `c` of the procedure, every instance with an oracle satisfying §2.1,
every optimal selector, `s₁ ∈ K`, `η > 0`, `ε ∈ (0, (α+2)R]`, `T ≥ 1` and `f₁, …, f_T ∈ 𝓕`,
every round `t ∈ {1, …, T}` of Algorithm 3 satisfies
`dist²(ỹ_{t+1}) ≤ dist²(ỹ_t) + 2ηF dist(ỹ_t) + η²F² − k_t ε² + ε²`, where dist is the distance
to CH(αK) and `k_t = (alg3Call … t).loops` is the number of loop passes of round t's Algorithm 2
call. This covers both α ≥ 1 (y_{t+1} = ỹ_t − ηf_t) and α < 1 (y_{t+1} = ỹ_t + ηf_t).

**Formalization Note.** The display's endpoints are stated. The paper fixes one universal
constant c; the recursion is stated for every `c > 0` (it uses only termination and the decrease
clause of Lemma 7, which hold for every `N ≥ 1`). -/
theorem dist_recursion :
    ∀ (c : ℝ), 0 < c →
    ∀ {d : ℕ} (S : Setting d) (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      IsApproxOracle S OK →
      ∀ (sel : (N : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin N → EuclideanSpace ℝ (Fin d)) → Fin N → ℝ),
      IsOptimalSelector sel →
      ∀ (s₁ : EuclideanSpace ℝ (Fin d)), s₁ ∈ S.K →
      ∀ (η ε : ℝ), 0 < η → 0 < ε → ε ≤ (S.α + 2) * S.R →
      ∀ (T : ℕ), 1 ≤ T →
      ∀ (f : ℕ → EuclideanSpace ℝ (Fin d)), (∀ t ∈ Finset.Icc 1 T, f t ∈ S.Fset) →
      ∀ t ∈ Finset.Icc 1 T,
        Metric.infDist (alg3Y S OK sel c s₁ η ε f (t + 1)) (convexHull ℝ (S.α • S.K)) ^ 2 ≤
          Metric.infDist (alg3Y S OK sel c s₁ η ε f t) (convexHull ℝ (S.α • S.K)) ^ 2 +
            2 * η * S.F * Metric.infDist (alg3Y S OK sel c s₁ η ε f t) (convexHull ℝ (S.α • S.K)) +
            η ^ 2 * S.F ^ 2 - ((alg3Call S OK sel c s₁ η ε f t).loops : ℝ) * ε ^ 2 + ε ^ 2 := by sorry

end GarberOLO.Alg3
