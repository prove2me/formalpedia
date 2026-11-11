-- Prove2me | Theorems.Thm_MinKCutII_Main_lemma_44
-- name    : MinKCutII.Main.lemma_44
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:40:04.416173+00:00
-- url     : https://prove2.me/theorems/a085dae0-f410-4cc4-9b98-673ce7a4308b
-- title:
--   Lemma 44 — a tree drawn from a k-cut packing (k − 1)-respects a light cut with probability Ω(1/k), with explicit constants
-- statement:
--   There is a universal $c_0>0$ with the following property. Let $F=(V,E,c)$ be connected with positive capacities, $3\le k\le|V|$, $0<\eta\le1/30$, and let $(y,z)$ be tree weights and edge slacks satisfying (1) and (2) of Lemma 43, $\tau=\sum_Ty_T$. Let $S$ be a cut with $c_F(S)\le2\lambda_k(F)/k$, and let $T$ be drawn with probability $y_T/\tau$. Then
--   $$\Pr\big[|\delta_T(S)|\le k-1\big]\ \ge\ \begin{cases}\dfrac{1-9\eta}{6(1-\eta)},&k=3,\\[2mm]\dfrac{1-4\eta}{3(1-\eta)},&k=4,\\[2mm]\dfrac1{k-1},&k\ge5,\end{cases}$$
--   and the probability is at least $c_0/k$.
--
--   It is the sampling guarantee behind the randomized reduction (Theorem 47).
--
--   Differences from the source:
--
--   - generalization: (y, z) the packing of Lemma 43 → every (y, z) with y ≥ 0 supported on spanning trees of F, z ≥ 0, satisfying (1) and (2) of Lemma 43; reason: the proof uses only (1) and (2); the packing computed by Lemma 43 is one such pair
--   - reading: Let k ≥ 3 … the packing of Lemma 43 → 3 ≤ k ≤ |V| and 0 < η; reason: Lemma 43 assumes 2 ≤ k ≤ n and 0 < η < 1/2
--   - reading: In particular, the probability is Ω(1/k) → a universal c₀ > 0, chosen before the graph and k, with probability ≥ c₀/k; reason: Ω(1/k) with an absolute constant
--   - encoding: T drawn with probability y_T/τ; Pr[·] → the ratio (Σ_{T: |δ_T(S)| ≤ k−1} y_T)/τ; reason: the probability of an event under the finite distribution y/τ
--   - reading: c_F(S) ≤ 2λ_k(F)/k → S a cut (nonempty, proper) with that bound; reason: S is a side of a cut
--   - generalization: positive integer or rational capacities (§2, §4.3) → positive real capacities; reason: integers and rationals are special cases
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 32, Lemma 44

import Mathlib
import Definitions.Def_MinKCutII_Main_KCut
import Definitions.Def_MinKCutII_Main_Cuts
import Definitions.Def_MinKCutII_Main_TreePacking

set_option autoImplicit false

open CombOpt.MinCut

namespace MinKCutII.Main

/-- **Lemma 44** (p. 32), for every packing satisfying (1)–(2) of Lemma 43. There is a universal
`c₀ > 0` such that: for a connected graph `F` with positive capacities, `3 ≤ k ≤ |V|`,
`0 < η ≤ 1/30`, weights `(y, z)` satisfying (1) and (2), and a cut `S` with `c_F(S) ≤ 2λ_k(F)/k`,
the probability `Pr[|δ_T(S)| ≤ k − 1]` for `T` drawn with probability `y_T/τ` is at least
`(1 − 9η)/(6(1 − η))` if `k = 3`, `(1 − 4η)/(3(1 − η))` if `k = 4`, `1/(k − 1)` if `k ≥ 5`, and at
least `c₀/k` (the "in particular" `Ω(1/k)`). -/
theorem lemma_44 :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (F : CapGraph V E) (k : ℕ)
        (η : ℝ) (y : Finset E → ℝ) (z : E → ℝ) (S : Finset V),
        PosCap F → IsConnected F → 3 ≤ k → k ≤ Fintype.card V → 0 < η → η ≤ 1 / 30 →
        IsKCutPacking F k η y z → IsCut S →
        (∃ L : ℝ, lam F k = (L : WithTop ℝ) ∧ cutVal F S ≤ 2 * L / k) →
        (k = 3 → (1 - 9 * η) / (6 * (1 - η)) ≤ respectMass F y S (k - 1) / packTotal y) ∧
        (k = 4 → (1 - 4 * η) / (3 * (1 - η)) ≤ respectMass F y S (k - 1) / packTotal y) ∧
        (5 ≤ k → 1 / ((k : ℝ) - 1) ≤ respectMass F y S (k - 1) / packTotal y) ∧
        c₀ / k ≤ respectMass F y S (k - 1) / packTotal y := by sorry

end MinKCutII.Main
