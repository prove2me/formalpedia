-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_lemma_4_2
-- name    : MinSumRadiiPTAS.Main.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:02:01.169763+00:00
-- url     : https://prove2.me/theorems/b71caa63-4d19-4d12-a11e-1f4fcab25210
-- title:
--   Lemma 4.2 — partial LDD: expected number of parts meeting a test ball $\le 1 + 2t\,r_B/(b-a)$
-- statement:
--   **Lemma 4.2** (p. 9). Let $d$ be a metric, $X \subseteq P$, the centers $Y$ listed without repetition in any fixed order, $0 \le a < b$, $B$ any ball (center in $P$, radius $r_B \ge 0$), $Y' \subseteq Y$, and $t$ the number of points of $Y'$ within distance $b + r_B$ of $c_B$. With $\ell$ uniform on $[a, b]$, the number of parts among $\{P_y : y \in Y'\} \cup \{P_{\mathrm{far}}\}$ of $\mathrm{LDD}(X, Y, a, b)$ that intersect $B$ is a measurable function of $\ell$, and its expectation $\frac{1}{b-a}\int_a^b(\cdot)\,d\ell$ is at most
--   $$1 + 2t\,\frac{r_B}{b - a}.$$
--
--   Differences from the source:
--   - encoding: point set P with |P| = n, a metric d on P → points Fin n (0-based), d : Fin n → Fin n → ℝ with the published MinSumClust.IsMetric (d(p,p)=0, d ≥ 0, symmetry, triangle inequality, d(p,q) > 0 for p ≠ q); reason: same instances
--   - encoding: balls Ball(c, r) with r ∈ ℝ≥0 and sets of balls → Ball n = (center : Fin n, radius : ℝ) with point set {p : d(c,p) ≤ r}; arbitrary input/output balls carry 0 ≤ radius explicitly; mathematical sets of balls are Finsets; reason: same objects; a negative radius is not a ball (p. 1)
--   - encoding: uniformly random radius ℓ ∈ [a, b] and E[·] → 0 ≤ a < b, and E as (b − a)⁻¹ times the lower Lebesgue integral over Icc a b of the count (in ℝ≥0∞), with measurability of the count as a conjunct; reason: the uniform law needs a < b and a radius is nonnegative; the lower integral of a measurable nonnegative function is its expectation
--   - encoding: "the number of parts in {P_y | y ∈ Y′} ∪ {P_far} that intersect B" → #{y ∈ Y′ : P_y ∩ B ≠ ∅} + [P_far ∩ B ≠ ∅]; reason: parts that meet B are nonempty and pairwise disjoint, so they are distinct elements of the set of parts
--   - generalization: normalised instance of §§3–7 (Lemma 2.1: integer distances, opt ≤ 8k/ε) → any metric on Fin n (no normalisation assumed); reason: the statement and its proof do not use the normalisation; it specializes to normalised instances
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §4, Lemma 4.2, p. 9

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumRadiiPTAS_Main_Partition

open scoped Classical ENNReal

namespace MinSumRadiiPTAS.Main

/-- **Lemma 4.2** (p. 9): let `B` be a ball, `Y′ ⊆ Y` and `t` the number of points of `Y′` within
distance `b + r_B` of `c_B`. For `LDD(X, Y, a, b)` with the centers `Y` in any fixed order `l` and
the radius `ℓ` uniform on `[a, b]`, the expected number of parts among `{P_y : y ∈ Y′} ∪ {P_far}`
that intersect `B` is at most `1 + 2t · r_B/(b − a)`. The count is a measurable function of `ℓ` and
the expectation is `(b − a)⁻¹ ∫_{[a,b]}` of it. -/
theorem lemma_4_2 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsMetric d)
    (X : Finset (Fin n)) (l : List (Fin n)) (hl : l.Nodup) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (B : Ball n) (hB : 0 ≤ B.radius) (Y' : Finset (Fin n)) (hY' : ∀ y ∈ Y', y ∈ l) :
    let t : ℕ := (Y'.filter (fun y => d B.center y ≤ b + B.radius)).card
    let parts : ℝ → ℕ := fun ℓ =>
      (Y'.filter (fun y => (lddPart d X l ℓ y ∩ B.pts d).Nonempty)).card +
        (if (lddFar d X l ℓ ∩ B.pts d).Nonempty then 1 else 0)
    Measurable (fun ℓ => (parts ℓ : ℝ)) ∧
      (∫⁻ ℓ in Set.Icc a b, ((parts ℓ : ℕ) : ℝ≥0∞)) / ENNReal.ofReal (b - a) ≤
        ENNReal.ofReal (1 + 2 * (t : ℝ) * B.radius / (b - a)) := by sorry

end MinSumRadiiPTAS.Main
