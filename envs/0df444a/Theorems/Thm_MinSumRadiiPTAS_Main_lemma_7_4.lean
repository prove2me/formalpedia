-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_lemma_7_4
-- name    : MinSumRadiiPTAS.Main.lemma_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:00:49.034553+00:00
-- url     : https://prove2.me/theorems/f7c7e5bf-d2ae-4cc4-9875-56d9fa51e1af
-- title:
--   Lemma 7.4 — MergeSolutions: $S$ covers $X$, $|S| \le \theta|S_1|+(1-\theta)|S_2|$, $\mathrm{cost}(S) \le F(1+2\varepsilon) + R/\varepsilon^2 + (144R/\varepsilon^2)\log_+(2\varepsilon^2 w/R)$
-- statement:
--   **Lemma 7.4** (pp. 28–29). Let $d$ be a metric, $\varepsilon \in (0, 1/10)$, $X \subseteq P$, and $(S_1, S_2, \theta)$ a bipoint solution for $X$: finite sets of balls with nonnegative radii, each covering $X$, and $\theta \in [0, 1]$. Let $R = \max_{B \in S_1 \cup S_2} r_B$ ($0$ if both are empty) and $w = \mathrm{cost}(S_1) + \mathrm{cost}(S_2)$. Then there is a finite set $S$ of balls with nonnegative radii (the output of MergeSolutions) such that
--   1. $S$ covers $X$,
--   2. $|S| \le \theta|S_1| + (1-\theta)|S_2|$, and
--   3. $\mathrm{cost}(S) \le \big(\theta\,\mathrm{cost}(S_1) + (1-\theta)\,\mathrm{cost}(S_2)\big)(1 + 2\varepsilon) + \dfrac{R}{\varepsilon^2} + \dfrac{144R}{\varepsilon^2}\log_+\Big(\dfrac{2\varepsilon^2 w}{R}\Big)$,
--
--   where $\log_+(z) = \max(0, \log z)$ (natural logarithm) and $\log_+(0) = 0$.
--
--   Differences from the source:
--   - encoding: point set P with |P| = n, a metric d on P → points Fin n (0-based), d : Fin n → Fin n → ℝ with the published MinSumClust.IsMetric (d(p,p)=0, d ≥ 0, symmetry, triangle inequality, d(p,q) > 0 for p ≠ q); reason: same instances
--   - encoding: balls Ball(c, r) with r ∈ ℝ≥0 and sets of balls → Ball n = (center : Fin n, radius : ℝ) with point set {p : d(c,p) ≤ r}; arbitrary input/output balls carry 0 ≤ radius explicitly; mathematical sets of balls are Finsets; reason: same objects; a negative radius is not a ball (p. 1)
--   - reading: "There is a procedure MergeSolutions whose output S satisfies 1–3" → for every input there exists a set S satisfying 1–3; reason: the procedure's running time is part of Theorem 7.3, not of Lemma 7.4; an output with 1–3 exists iff some procedure produces one
--   - encoding: log₊(2ε²w/R) at R = 0 → logPlus (2ε²w/R) with Lean's x/0 = 0, i.e. log₊(0) = 0; reason: the printed convention log₊(0) = 0
--   - generalization: normalised instance of §§3–7 (Lemma 2.1: integer distances, opt ≤ 8k/ε) → any metric on Fin n (no normalisation assumed); reason: the statement and its proof do not use the normalisation; it specializes to normalised instances
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §7.1, Lemma 7.4, pp. 28–29

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-- **Lemma 7.4** (MergeSolutions, pp. 28–29): for `ε ∈ (0, 1/10)`, a client set `X ⊆ P` and a
bipoint solution `(S₁, S₂, θ)` for `X` (finite sets of balls with nonnegative radii, each covering
`X`, `θ ∈ [0, 1]`), with `R = max_{B ∈ S₁ ∪ S₂} r_B` (`0` if both are empty) and
`w = cost(S₁) + cost(S₂)`, there is a set `S` of balls (nonnegative radii) that
1. covers `X`,
2. has `|S| ≤ θ|S₁| + (1 − θ)|S₂|`, and
3. has `cost(S) ≤ (θ cost(S₁) + (1 − θ) cost(S₂))(1 + 2ε) + R/ε² + (144R/ε²) log₊(2ε²w/R)`,
with `log₊(z) = max(0, log z)` (natural logarithm) and `log₊(0) = 0`. -/
theorem lemma_7_4 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsMetric d) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 10) (X : Finset (Fin n)) (S1 S2 : Finset (Ball n))
    (hS1 : ∀ B ∈ S1, 0 ≤ B.radius) (hS2 : ∀ B ∈ S2, 0 ≤ B.radius) (hc1 : Covers d S1 X)
    (hc2 : Covers d S2 X) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let R : ℝ := if h : (S1 ∪ S2).Nonempty then (S1 ∪ S2).sup' h Ball.radius else 0
    let w : ℝ := cost S1 + cost S2
    ∃ S : Finset (Ball n), (∀ B ∈ S, 0 ≤ B.radius) ∧ Covers d S X ∧
      (S.card : ℝ) ≤ θ * S1.card + (1 - θ) * S2.card ∧
      cost S ≤ (θ * cost S1 + (1 - θ) * cost S2) * (1 + 2 * ε) + R / ε ^ 2 +
        144 * R / ε ^ 2 * logPlus (2 * ε ^ 2 * w / R) := by sorry

end MinSumRadiiPTAS.Main
