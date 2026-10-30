-- Prove2me | Theorems.Thm_GarberOLO_Alg3_lemma7
-- name    : GarberOLO.Alg3.lemma7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:03:17.54162+00:00
-- url     : https://prove2.me/theorems/499116f7-7140-42fd-bde3-7695b6553e42
-- title:
--   Lemma 7 (corrected: $4\alpha^2R^2$, at most $1 + 4\alpha^2R^2/\varepsilon^2$ passes, floored query count)
-- statement:
--   Throughout, $K, \mathcal F \subset \mathbb R^d_+$ are compact, $\|x\| \le R$ on $K$, $\|f\| \le F$ on $\mathcal F$, $0 \le x\cdot f \le C$ on $K \times \mathcal F$ ($R, F, C > 0$), and $\mathcal O_K$ is an $\alpha$-approximate linear optimization oracle for $K$ ($\alpha > 0$; §2.1).
--
--   There is $c_0 > 0$ such that for every procedure constant $c \ge c_0$ there is $C > 0$ with the following property. Let $y \in \mathbb R^d$ and $\varepsilon \in (0, (\alpha+2)R]$, and run Algorithm 2 on $(y, \varepsilon)$ with $N$ prescribed as in Lemma 5 at the current point and an optimal solution of Problem (5). Then Algorithm 2 terminates; if the loop was entered $k$ times and it returns $\tilde y$, $(a_1, \dots, a_N)$ and $(v_1, s_1), \dots, (v_N, s_N)$:
--
--   1. $k \le 1 + 4\alpha^2R^2/\varepsilon^2$;
--   2. $(a_1,\dots,a_N)$ is a probability distribution;
--   3. $\|\tilde y - z\|^2 \le \|y - z\|^2$ for every $z \in \mathrm{CH}(\alpha K)$;
--   4. $\|p - \tilde y\| \le 3\varepsilon$ for $p = \sum_{i=1}^N a_i v_i$;
--   5. $\mathrm{dist}^2(\tilde y, \mathrm{CH}(\alpha K)) \le \min\{4\alpha^2R^2,\ \mathrm{dist}^2(y, \mathrm{CH}(\alpha K)) - (k-1)\varepsilon^2\}$;
--   6. the total number of oracle calls is at most $C\, k \max\{1,d\}^2 \max\{1, \ln((\alpha+1)R/\varepsilon)\}$.
--
--   Algorithm 2 is an oracle-efficient infeasible projection: each extra pass of its loop moves the point $\varepsilon^2$ closer (in squared distance) to $\mathrm{CH}(\alpha K)$, which is what makes the average number of passes in Algorithm 3 small.
--
--   Differences from the source:
--   - correction: dist²(ỹ, CH(αK)) ≤ min{2α²R², …} → min{4α²R², …}; reason: the printed bound is false: d = 1, K = 𝓕 = {1}, R = F = C = α = 1, O_K ≡ 1, y = −1, ε = 3 = (α+2)R satisfy every assumption; Problem (4) is infeasible, so k = 1, ỹ = −1 and dist² = 4 > 2; ỹ₁ and CH(αK) share only the ball B(0, αR), which gives 4α²R² (paper.md Correction 2)
--   - correction: Algorithm 2 terminates after at most ⌈α²R²/ε²⌉ iterations → k ≤ 1 + 4α²R²/ε²; reason: same instance with ε = 1 and any c ≥ 3: the loop is entered k = 3 > 1 = ⌈α²R²/ε²⌉ times (exact bisection run, planning_numerics case B); the proof's own decrease (k−1)ε² ≤ dist²(ỹ₁) ≤ 4α²R² gives the corrected bound (paper.md Correction 3)
--   - correction: overall number of queries O(k d² ln((α+1)R/ε)) → ≤ C k max{1,d}² max{1, ln((α+1)R/ε)}; reason: for ε = (α+1)R the logarithm is 0 (and for d = 0 the factor d² is 0) while at least one call is made (same instance, ε = 2: k = 1, one call); the floors change nothing for d ≥ 1 and ε ≤ (α+1)R/e (paper.md Corrections 1, 3)
--   - reading: "returning … a distribution (a₁, …, a_N)" → clause: a is a probability vector; reason: explicit form of "distribution"
--   - generalization: c a (fixed) positive universal constant for which Lemma 5 holds → ∃ c₀ > 0, ∀ c ≥ c₀, ∃ C > 0 (C depends only on c); reason: every c ≥ c₀ satisfies Lemma 5's requirement, so the statement specializes to the paper's c (paper.md Reading 2)
--   - encoding: c is a positive universal constant; O(·) → the constants are quantified before the dimension d and every datum of the instance; reason: this is what "universal" and O(·) mean; constants chosen after the instance would make the bounds trivial
--   - reading: "the Ellipsoid method" (Lemma 5, p. 9), not specified further → the central-cut Ellipsoid method from E₀ = B(0,1) (ellipsoidCut, sdState), with bisection for d = 1 and no change on a zero cut vector; reason: E₀ = B(0,1) is the ball of Problem (4)'s constraint, which the proof on p. 11 needs (B(h/2, r) ⊂ B(0,1)); the standard update divides by d² − 1 = 0 when d = 1; a zero cut arises only when v = x, and then p = x (paper.md Reading 1)
--   - reading: N "as prescribed in Lemma 5" (Algorithm 2, line 8), any positive integer N ≥ c d² ln(((α+1)R + ‖x‖)/ε) → N = Nprescribed S c ε ỹ = max{1, ⌈c d² ln(((α+1)R + ‖ỹ‖)/ε)⌉}, recomputed at the current ỹ of each loop pass; reason: with N unbounded the oracle-call count is unbounded, so the least admissible N is the only reading under which the call bounds can hold (paper.md Reading 2)
--   - reading: "an optimal solution" of Problem (5), "some point" s₁ ∈ K, and the oracle O_K → arbitrary: every selector sel with IsOptimalSelector sel, every s₁ ∈ K, every OK with IsApproxOracle S OK; reason: the paper leaves these choices free and claims the result for every choice (paper.md Reading 5)
--   - encoding: dist(x, CH(αK)) = min_{z∈CH(αK)} ‖z − x‖ (§2.2) → Metric.infDist x (convexHull ℝ (α • K)); reason: CH(αK) is nonempty (an oracle value lies in K) and compact, so the infimum is the attained minimum
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Lemma 7, p. 12

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_IsApproxOracle
import Definitions.Def_GarberOLO_Alg3_IsOptimalSelector
import Definitions.Def_GarberOLO_Alg3_alg2Terminates
import Definitions.Def_GarberOLO_Alg3_alg2

open scoped Pointwise

namespace GarberOLO.Alg3

/-- **Lemma 7 (corrected: 4α²R² and 1 + 4α²R²/ε² for 2α²R² and ⌈α²R²/ε²⌉; floors in the query
count).**
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 7, p. 12: "Fix y ∈ ℝᵈ and ε ∈ (0, (α + 2)R]. Algorithm 2 terminates after at most
⌈α²R²/ε²⌉ iterations, returning a point ỹ ∈ ℝᵈ, a distribution (a₁, …, a_N) and a set
{(v₁, s₁), …, (v_N, s_N)} outputted by the extended approximation oracle, where N is as defined in
Lemma 5, such that 1. ∀ z ∈ CH(αK) : ‖ỹ − z‖² ≤ ‖y − z‖², 2. ‖p − ỹ‖ ≤ 3ε for p := Σ_{i=1}^N aᵢvᵢ.
Moreover, if the for loop was entered a total number of k times, then the final value of ỹ
satisfies dist²(ỹ, CH(αK)) ≤ min{2α²R², dist²(y, CH(αK)) − (k − 1)ε²}, and the overall number of
queries to the approximation oracle is O(kd² ln((α+1)R/ε))."

There is `c₀ > 0` such that for every `c ≥ c₀` there is `C > 0` with the following property.
For every instance with an oracle satisfying §2.1, every optimal selector for Problem (5), every
`y` and every `ε ∈ (0, (α+2)R]`, Algorithm 2 run with `N = Nprescribed S c ε ỹ` terminates, and
its output `o` (with `k = o.loops`) satisfies: `k ≤ 1 + 4α²R²/ε²`; `a` is a probability vector;
item 1; item 2; `dist²(ỹ, CH(αK)) ≤ min{4α²R², dist²(y, CH(αK)) − (k − 1)ε²}`; and the number of
oracle calls is at most `C · k · max{1,d}² · max{1, ln((α+1)R/ε)}`.

**Formalization Note.** Corrections 2 and 3 of the mission: 2α²R² is false (d = 1, K = 𝓕 = {1},
α = R = 1, y = −1, ε = 3: k = 1, dist² = 4), and so is ⌈α²R²/ε²⌉ (same instance, ε = 1, c ≥ 3:
k = 3); the query count is floored as in Theorem 1 (Correction 1). CH(αK) is
`convexHull ℝ (α • K)`, dist is `Metric.infDist` (CH(αK) is nonempty and compact). -/
theorem lemma7 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∃ C : ℝ, 0 < C ∧
    ∀ {d : ℕ} (S : Setting d) (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      IsApproxOracle S OK →
      ∀ (sel : (N : ℕ) → EuclideanSpace ℝ (Fin d) → (Fin N → EuclideanSpace ℝ (Fin d)) → Fin N → ℝ),
      IsOptimalSelector sel →
      ∀ (y : EuclideanSpace ℝ (Fin d)) (ε : ℝ), 0 < ε → ε ≤ (S.α + 2) * S.R →
        alg2Terminates S OK c ε y ∧
        ((alg2 S OK sel c ε y).loops : ℝ) ≤ 1 + 4 * S.α ^ 2 * S.R ^ 2 / ε ^ 2 ∧
        ((∀ i, 0 ≤ (alg2 S OK sel c ε y).a i) ∧ ∑ i, (alg2 S OK sel c ε y).a i = 1) ∧
        (∀ z ∈ convexHull ℝ (S.α • S.K),
          ‖(alg2 S OK sel c ε y).yt - z‖ ^ 2 ≤ ‖y - z‖ ^ 2) ∧
        ‖∑ i, (alg2 S OK sel c ε y).a i • ((alg2 S OK sel c ε y).vs i).1 -
            (alg2 S OK sel c ε y).yt‖ ≤ 3 * ε ∧
        Metric.infDist (alg2 S OK sel c ε y).yt (convexHull ℝ (S.α • S.K)) ^ 2 ≤
          min (4 * S.α ^ 2 * S.R ^ 2)
            (Metric.infDist y (convexHull ℝ (S.α • S.K)) ^ 2 -
              (((alg2 S OK sel c ε y).loops : ℝ) - 1) * ε ^ 2) ∧
        ((alg2 S OK sel c ε y).calls : ℝ) ≤
          C * ((alg2 S OK sel c ε y).loops : ℝ) * (max 1 (d : ℝ)) ^ 2 *
            max 1 (Real.log ((S.α + 1) * S.R / ε)) := by sorry

end GarberOLO.Alg3
