-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_lemma_3_1
-- name    : MinSumRadiiPTAS.Main.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:06:00.781304+00:00
-- url     : https://prove2.me/theorems/c410c853-219d-4751-bba4-16647fcd0785
-- title:
--   Lemma 3.1 — greedy rounding of the Lagrangian LP: $S'$ covers $X$ and $\mathrm{cost}_\lambda(S') \le 3\,\mathrm{opt}_{f,\lambda}(X)$
-- statement:
--   **Lemma 3.1** (p. 8). Let $d$ be a metric on $P$, $\lambda \ge 0$ and $X \subseteq P$. Let $x$ be any optimal solution of (Lagrangian-LP) for $X$, and let the greedy rounding process the balls $B \in \mathfrak B$ with $x_B > 0$ in any order of nonincreasing radius, keeping a ball iff it intersects no ball kept before, and output $S' = \{\mathrm{Ball}(c_B, 3r_B) : B \text{ kept}\}$. Then $S'$ covers $X$ and
--   $$\mathrm{cost}_\lambda(S') \le 3\,\mathrm{opt}_{f,\lambda}(X).$$
--
--   Differences from the source:
--   - encoding: point set P with |P| = n, a metric d on P → points Fin n (0-based), d : Fin n → Fin n → ℝ with the published MinSumClust.IsMetric (d(p,p)=0, d ≥ 0, symmetry, triangle inequality, d(p,q) > 0 for p ≠ q); reason: same instances
--   - encoding: balls Ball(c, r) with r ∈ ℝ≥0 and sets of balls → Ball n = (center : Fin n, radius : ℝ) with point set {p : d(c,p) ≤ r}; arbitrary input/output balls carry 0 ≤ radius explicitly; mathematical sets of balls are Finsets; reason: same objects; a negative radius is not a ball (p. 1)
--   - reading: "the above greedy rounding algorithm" run on "an optimal pair (x, y)", balls in decreasing order of radii → every optimal primal x and every processing list of the balls with x_B > 0 that is nonincreasing in radius (IsGreedyOrder); reason: the paper fixes neither the optimal solution nor the order among equal radii; the dual y is not used by the output
--   - encoding: opt_{f,λ}(X), the optimum of the packing dual → optf, the infimum of the primal objective over the feasible set; reason: equal by LP strong duality (both programs feasible and bounded)
--   - generalization: normalised instance of §§3–7 (Lemma 2.1: integer distances, opt ≤ 8k/ε) → any metric on Fin n (no normalisation assumed); reason: the statement and its proof do not use the normalisation; it specializes to normalised instances
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §3, Lemma 3.1, p. 8 (algorithm p. 7)

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumRadiiPTAS_Main_LP

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-- **Lemma 3.1** (p. 8): for any client set `X ⊆ P` and opening cost `λ ≥ 0`, the greedy rounding
of §3 — run on any optimal solution `x` of (Lagrangian-LP) for `X`, processing the balls of `𝔅` with
`x_B > 0` in any nonincreasing order of radius — outputs balls `S′` that cover `X` with
`cost_λ(S′) ≤ 3 opt_{f,λ}(X)`. -/
theorem lemma_3_1 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsMetric d) (lam : ℝ)
    (hlam : 0 ≤ lam) (X : Finset (Fin n)) (x : Ball n → ℝ) (hx : IsOptimalLP d lam X x)
    (l : List (Ball n)) (hl : IsGreedyOrder d x l) :
    CoversL d (greedyRound d l) X ∧ lcostL lam (greedyRound d l) ≤ 3 * optf d lam X := by sorry

end MinSumRadiiPTAS.Main
