-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_theorem_7_3
-- name    : MinSumRadiiPTAS.Main.theorem_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:02:20.591116+00:00
-- url     : https://prove2.me/theorems/ed0a4668-6b91-411a-bbc9-0856322d6800
-- title:
--   Theorem 7.3 — polynomial-time bipoint rounding: $|S_{mix}| \le \theta|S_1|+(1-\theta)|S_2|$, $\mathrm{cost}(S_{mix}) \le (1+C\varepsilon)\mathrm{cost}(S_{bp}) + C R/\varepsilon^3$
-- statement:
--   **Theorem 7.3** (p. 28; proof p. 34). There are one admissible program $P$ of the randomized distance-oracle real RAM and absolute constants $c, C$ such that, for every $\varepsilon \in (0, 1/10)$, every metric $d$ on $P$, every $X \subseteq P$ and every bipoint solution $(S_1, S_2, \theta)$ for $X$ (lists of balls with nonnegative radii, each covering $X$, $\theta \in [0, 1]$; input: $\theta$ in real memory, $X$ as a 0/1 array, $S_1, S_2$ as ball lists), on every random tape the run has halted after $c\,(N + |S_1| + |S_2|)^c$ steps ($N = \max(n, 2)$), with work at most that, having output a list $S_{mix}$ of balls that covers $X$, with
--   $$|S_{mix}| \le \theta|S_1| + (1-\theta)|S_2| \quad\text{and}\quad \mathrm{cost}(S_{mix}) \le (1 + C\varepsilon)\,\mathrm{cost}(S_{bp}) + C\,\frac{R}{\varepsilon^3}$$
--   for every $R \ge 0$ that bounds the radii of all balls of $S_1$ and $S_2$, where $\mathrm{cost}(S_{bp}) = \theta\,\mathrm{cost}(S_1) + (1-\theta)\,\mathrm{cost}(S_2)$.
--
--   Differences from the source:
--   - encoding: point set P with |P| = n, a metric d on P → points Fin n (0-based), d : Fin n → Fin n → ℝ with the published MinSumClust.IsMetric (d(p,p)=0, d ≥ 0, symmetry, triangle inequality, d(p,q) > 0 for p ≠ q); reason: same instances
--   - encoding: balls Ball(c, r) with r ∈ ℝ≥0 and sets of balls → Ball n = (center : Fin n, radius : ℝ) with point set {p : d(c,p) ≤ r}; arbitrary input/output balls carry 0 ≤ radius explicitly; mathematical sets of balls are Finsets; reason: same objects; a negative radius is not a ball (p. 1)
--   - encoding: a set S of balls output by an algorithm, |S|, cost(S) → a ball list read from the machine; |S| is its length and cost(S) the sum over its entries, a repeated ball counted every time; reason: an output without repetitions is a set; counting repetitions only makes the size and cost bounds harder to meet
--   - generalization: a (randomized, polynomial-time) algorithm on an unspecified machine → one MinSumFPT.Admissible program of the published randomized distance-oracle real RAM (unit cost per instruction; no floor, √, log/exp or pointer multiplication; rational literals); inputs in the published initState layout (n, k, ε, δ = 0); reason: the machine has fewer primitives than any standard real RAM, so the statement implies the same statement on a richer machine
--   - generalization: "Fix ε ∈ (0, 1/10). There is an algorithm …" (an algorithm per ε) → one program P and constants chosen before ε, with ε as input in mem 0; reason: a single program for all ε specializes to an algorithm for each fixed ε; the proof's algorithm takes ε as a parameter
--   - reading: "polynomial time" → at most c · N^c steps (resp. c · (N + |S₁| + |S₂|)^c) with c absolute, fixed before ε and the input; reason: polynomial in the input size with a degree independent of the input
--   - reading: (1 + O(ε)) cost(S_bp) + O(R/ε³) → (1 + C ε) cost(S_bp) + C R/ε³ with C absolute, fixed before ε and the input; reason: O(·) in a statement for every ε ∈ (0, 1/10) has absolute constants
--   - encoding: "a polynomial-time algorithm" (deterministic) → the guarantee holds on every random tape; reason: a program correct on every tape is correct on the all-zero tape, i.e. deterministically
--   - encoding: "each cluster in S_1, S_2 has radius at most R" → the cost bound for every R ≥ 0 bounding all radii (R is not an input); reason: R is a radius bound, so nonnegative; the output does not depend on R
--   - generalization: bipoint solution of sets S_1, S_2 of balls → input lists S_1, S_2, possibly with repetitions, |S_i| the list length and cost(S_i) counted with repetitions; reason: on lists without repetitions this is the paper's statement; with repetitions the bounds only get larger
--   - generalization: normalised instance of §§3–7 (Lemma 2.1: integer distances, opt ≤ 8k/ε) → any metric on Fin n (no normalisation assumed); reason: the statement and its proof do not use the normalisation; it specializes to normalised instances
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §7, Theorem 7.3, p. 28 (proof p. 34)

import Mathlib
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumRadiiPTAS_Main_Machine

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-- **Theorem 7.3** (p. 28; proof p. 34): one admissible program `P` and absolute constants `c, C`
such that, for every `ε ∈ (0, 1/10)`, every metric on `Fin n`, every client set `X` and every bipoint
solution `(S₁, S₂, θ)` for `X` (ball lists with nonnegative radii, each covering `X`, `θ ∈ [0, 1]`;
input: `θ` in real memory, `X` as a 0/1 array, `S₁, S₂` as ball lists), on every tape the run has
halted after `c (N + |S₁| + |S₂|)^c` steps (`N = max(n, 2)`) with a ball list `S_mix` covering `X`,
with `|S_mix| ≤ θ|S₁| + (1 − θ)|S₂|`, and with
`cost(S_mix) ≤ (1 + Cε)(θ cost(S₁) + (1 − θ) cost(S₂)) + C R/ε³` for every `R ≥ 0` bounding all
radii of `S₁` and `S₂`. -/
theorem theorem_7_3 :
    ∃ P : MinSumFPT.Program, MinSumFPT.Admissible P ∧ ∃ c C : ℕ,
      ∀ ε : ℝ, 0 < ε → ε < 1 / 10 →
      ∀ (n k : ℕ) (d : Fin n → Fin n → ℝ), MinSumClust.IsMetric d →
      ∀ (X : Finset (Fin n)) (S1 S2 : List (Ball n)), (∀ B ∈ S1 ++ S2, 0 ≤ B.radius) →
        CoversL d S1 X → CoversL d S2 X →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        let T : ℕ := c * (max n 2 + S1.length + S2.length) ^ c
        ∀ ω : ℕ → ℝ, ∃ S : List (Ball n),
          OutputsBalls (runExt P n k ε [θ] X [S1, S2] d ω T) S ∧
            (runExt P n k ε [θ] X [S1, S2] d ω T).work ≤ T ∧
            CoversL d S X ∧
            (S.length : ℝ) ≤ θ * S1.length + (1 - θ) * S2.length ∧
            ∀ R : ℝ, 0 ≤ R → (∀ B ∈ S1 ++ S2, B.radius ≤ R) →
              lcost S ≤ (1 + (C : ℝ) * ε) * (θ * lcost S1 + (1 - θ) * lcost S2) +
                (C : ℝ) * R / ε ^ 3 := by sorry

end MinSumRadiiPTAS.Main
