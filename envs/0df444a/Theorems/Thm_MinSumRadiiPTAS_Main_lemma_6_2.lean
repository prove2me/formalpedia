-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_lemma_6_2
-- name    : MinSumRadiiPTAS.Main.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:06:15.7911+00:00
-- url     : https://prove2.me/theorems/316e9702-f911-49cf-8509-d22c75053cc5
-- title:
--   Lemma 6.2 — Case I ($\lambda \ge 6R$): a polynomial-time cover with radii $\le 6R$ and $\mathrm{cost}_\lambda(S) \le \mathrm{cost}_\lambda(O_R)$
-- statement:
--   **Lemma 6.2** (p. 24). There are one admissible program $P$ of the randomized distance-oracle real RAM and one absolute constant $c$ such that, for every $\varepsilon \in (0, 1/10)$, every normalised instance $(n, k, d)$, every opening cost $\lambda \in [\varepsilon/k, 10k/\varepsilon]$, every radius bound $R \ge 0$ with $\lambda \ge 6R$ and every client set $P' \subseteq P$ (input: $\lambda, R$ in real memory, $P'$ as a 0/1 array), on every random tape the run has halted after $c \cdot N^c$ steps ($N = \max(n, 2)$), with work at most that, having output a list $S$ of balls that covers $P'$, has all radii in $[0, 6R]$ and satisfies
--   $$\mathrm{cost}_\lambda(S) \le \mathrm{cost}_\lambda(O_R)$$
--   for every optimal cover $O_R$ of $P'$ by balls of $\mathfrak B$ of radius at most $R$.
--
--   Differences from the source:
--   - encoding: point set P with |P| = n, a metric d on P → points Fin n (0-based), d : Fin n → Fin n → ℝ with the published MinSumClust.IsMetric (d(p,p)=0, d ≥ 0, symmetry, triangle inequality, d(p,q) > 0 for p ≠ q); reason: same instances
--   - encoding: balls Ball(c, r) with r ∈ ℝ≥0 and sets of balls → Ball n = (center : Fin n, radius : ℝ) with point set {p : d(c,p) ≤ r}; arbitrary input/output balls carry 0 ≤ radius explicitly; mathematical sets of balls are Finsets; reason: same objects; a negative radius is not a ball (p. 1)
--   - encoding: a set S of balls output by an algorithm, |S|, cost(S) → a ball list read from the machine; |S| is its length and cost(S) the sum over its entries, a repeated ball counted every time; reason: an output without repetitions is a set; counting repetitions only makes the size and cost bounds harder to meet
--   - generalization: a (randomized, polynomial-time) algorithm on an unspecified machine → one MinSumFPT.Admissible program of the published randomized distance-oracle real RAM (unit cost per instruction; no floor, √, log/exp or pointer multiplication; rational literals); inputs in the documented extended layout initStateExt; reason: the machine has fewer primitives than any standard real RAM, so the statement implies the same statement on a richer machine
--   - reading: the lemma's own sentence (context of §6) → explicit hypotheses: StandingInstance d k ε (Lemma 2.1's normalisation: integer distances in [1, ⌈10k/ε⌉], opt ≤ 8k/ε, 1 ≤ k ≤ n), ε ∈ (0, 1/10), λ ∈ [ε/k, 10k/ε] (Theorem 6.1); reason: p. 7 assumes the normalisation for the rest of the paper, p. 6 fixes ε ∈ (0, 1/10), and §6 works under Theorem 6.1's λ; trap 19 (section standing assumptions are binders)
--   - reading: "polynomial time" → at most c · N^c steps (resp. c · (N + |S₁| + |S₂|)^c) with c absolute, fixed before ε and the input; reason: polynomial in the input size with a degree independent of the input
--   - encoding: "a polynomial time algorithm" (deterministic) → the guarantee holds on every random tape; reason: a program correct on every tape is correct on the all-zero tape, i.e. deterministically, and conversely
--   - encoding: radius bound R → 0 ≤ R; reason: p. 23 introduces OPT^R_λ(P′) "for some R ≥ 0"
--   - encoding: cost_λ(O_R) for the optimal solution O_R → for every optimal cover O_R (IsOptCover); reason: all optimal covers have the same cost_λ
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §6.1, Lemma 6.2, p. 24

import Mathlib
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumRadiiPTAS_Main_LP
import Definitions.Def_MinSumRadiiPTAS_Main_Machine

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-- **Lemma 6.2** (Case I, p. 24): one admissible program `P` and one absolute constant `c` such
that, on every normalised instance with `ε ∈ (0, 1/10)`, every opening cost `λ ∈ [ε/k, 10k/ε]`,
every radius bound `R ≥ 0` with `λ ≥ 6R` and every client set `P′` (input: `λ, R` in real memory,
`P′` as a 0/1 array), on every tape the run has halted after `c · N^c` steps (`N = max(n, 2)`) with a
ball list `S` covering `P′`, all radii in `[0, 6R]`, and `cost_λ(S) ≤ cost_λ(O_R)` for every optimal
cover `O_R` of `P′` by balls of `𝔅` of radius `≤ R`. -/
theorem lemma_6_2 :
    ∃ P : MinSumFPT.Program, MinSumFPT.Admissible P ∧ ∃ c : ℕ,
      ∀ ε : ℝ, 0 < ε → ε < 1 / 10 →
      ∀ (n k : ℕ) (d : Fin n → Fin n → ℝ), StandingInstance d k ε →
      ∀ lam R : ℝ, ε / k ≤ lam → lam ≤ 10 * k / ε → 0 ≤ R → 6 * R ≤ lam →
      ∀ P1 : Finset (Fin n),
        let T : ℕ := c * (max n 2) ^ c
        ∀ ω : ℕ → ℝ, ∃ S : List (Ball n),
          OutputsBalls (runExt P n k ε [lam, R] P1 [] d ω T) S ∧
            (runExt P n k ε [lam, R] P1 [] d ω T).work ≤ T ∧
            CoversL d S P1 ∧ (∀ B ∈ S, B.radius ≤ 6 * R) ∧
            ∀ OR : Finset (Ball n), IsOptCover d lam (fun B => B.radius ≤ R) P1 OR →
              lcostL lam S ≤ costL lam OR := by sorry

end MinSumRadiiPTAS.Main
