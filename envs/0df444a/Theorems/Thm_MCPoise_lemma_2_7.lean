-- Prove2me | Theorems.Thm_MCPoise_lemma_2_7
-- name    : MCPoise.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:34:27.351305+00:00
-- url     : https://prove2.me/theorems/059384bd-7ea6-4211-94d7-10f5aaced0df
-- title:
--   Lemma 2.7 — multi-root rounding: degree $O((L_\Delta + L'_d)\log k)$ and distance $O(L'_d \log k)$
-- statement:
--   Let $G$ be a graph with roots $r_1, \dots, r_\mu$, terminal sets $S_j \subseteq V \setminus \{r_j\}$ with $|S_j| \le 2k$, parameters $L_\Delta, L'_d$, and an explicitly represented feasible solution to Multiroot-LP.
--
--   **Lemma 2.7.** In polynomial time one finds a subgraph $H \subseteq G$ of maximum degree $O((L_\Delta + L'_d) \log k)$ in which, for all $j$, the root $r_j$ is connected by a path of length $O(L'_d \log k)$ to each $t \in S_j$.
--
--   **Formalization Note** The machine and the constant are fixed before the input, and $k$ is any bound on the sizes.
--
--   Differences from the source:
--   - reading: an efficient, polynomial-time algorithm → one deterministic machine `Turing.TM2ComputableInPolyTime`, polynomial in a fixed binary encoding on every input; reason: the source names no machine, and every step it describes is deterministic
--   - reading: the printed $O(\cdot)$ in $\log k$ → the factor $\log(k+1)$ with one absolute constant; reason: $\log k$ vanishes at $k = 1$, and for $k \ge 2$ the two differ by a constant factor
--   - encoding: parameters L_∆, L′_d; explicitly represented solution with polynomial support → L_∆ rational and ≥ 0, L′_d a natural number; the solution as lists of entries, part of the input length; reason: a rational L′_d has the same path sets as its floor, for which the conclusion is stronger; L_∆ ≥ 0 follows from the LP unless V is empty
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.7, p.15

import Mathlib
import Definitions.Def_MCPoise_maxDeg
import Definitions.Def_LCPlanarSteiner_sgOf
import Definitions.Def_MCPoise_MRIn

namespace MCPoise

/-- **Lemma 2.7 (multi-root rounding).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.7, p.15: "Suppose we are given a graph G = (V, E), roots r₁, . . . , r_µ ∈ V, terminal sets S_j ⊆ V \ {r_j} with |S_j| ≤ 2k for every j ∈ [µ], parameters L_∆, L′_d, and an explicitly represented feasible
solution to (Multiroot-LP) with polynomial support. Then, in polynomial time, we can find a subgraph H ⊆ G with max degree O((L_∆ + L′_d) log k) in which for all j ∈ [µ], r_j is connected via a path of length at most
O(L′_d log k) to each t ∈ S_j."

One machine and one absolute constant `C`, for every feasible input and every `k` with all `|S_j| ≤ 2k`.

**Formalization Note.** `k` bounds the sizes and is no input, so it is quantified after the output. Roots may coincide and a vertex may lie in several `S_j`. `log(k + 1)` replaces `log k`, which vanishes at `k = 1`; for `k = 0` all
`S_j` are empty and the factor forces `H` to have no edge. -/
theorem lemma_2_7 :
    ∃ alg : MRIn → List (ℕ × ℕ), Nonempty (Turing.TM2ComputableInPolyTime encMRIn encOut alg) ∧
      ∃ C : ℝ, ∀ R : MRIn, R.Feasible → ∀ k : ℕ, (∀ j, (R.S j).card ≤ 2 * k) →
        LCPlanarSteiner.sgOf R.n (alg R) ≤ R.graph ∧
        (maxDeg (LCPlanarSteiner.sgOf R.n (alg R)) : ℝ) ≤
          C * (((R.LΔ : ℝ) + (R.Lp : ℝ)) * Real.log ((k : ℝ) + 1)) ∧
        ∀ j, ∀ t ∈ R.S j, ∃ w : (LCPlanarSteiner.sgOf R.n (alg R)).Walk (R.r j) t,
          (w.length : ℝ) ≤ C * ((R.Lp : ℝ) * Real.log ((k : ℝ) + 1)) := by sorry

end MCPoise
