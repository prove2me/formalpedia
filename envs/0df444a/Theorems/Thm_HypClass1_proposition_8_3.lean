-- Prove2me | Theorems.Thm_HypClass1_proposition_8_3
-- name    : HypClass1.proposition_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:37:59.449339+00:00
-- url     : https://prove2.me/theorems/1d065246-613c-4103-a9a3-0f4153c3b660
-- title:
--   Proposition 8.3 — partition of $R$ into $(1\pm1/k^2)rn^2/2$ matchings, almost all large
-- statement:
--   Let $C$ be a sufficiently large constant and $n$ a sufficiently large integer. Let $\varepsilon, \delta, p, q, r, \lambda \in [0,1]$ and let $k$ be a positive integer with
--   $$
--   \log n \le k \le n^{0.01},\quad \varepsilon \le \frac1{k^2},\quad \delta \ge \frac{C^3}{k^2},\quad p \ge 0.01,\quad \frac{k^7\log n}{n} \le r \le \frac1{k^6},\quad q \ge C^4 k r \log^3 n,\quad \frac{C\log n}{n} \le \lambda \le \frac{r}{3k^2}. \tag{17}
--   $$
--   Let $S \subseteq [n]$ with $|S| = n/100$. Let $H$ and $R$ be edge-disjoint 3-graphs on $[n]$ such that $H$ is $(\varepsilon, p, n)$-pseudorandom, $\Delta_2(R) \le Crn$, and
--   $$
--   \deg_H(u) = \frac{pn^2}{2} \pm \lambda n^2, \qquad \deg_R(u) = \frac{rn^2}{2} \pm \lambda n^2 \qquad \text{for every } u \in [n].
--   $$
--
--   Then there is a partition $R = E_1 \cup \dots \cup E_s$ into matchings with
--   $$
--   s = \left(1 \pm \frac1{k^2}\right)\frac{rn^2}{2},
--   $$
--   and all but at most $s/k$ of the matchings $E_i$ satisfy $|E_i| \ge n/3 - n/k$.
--
--   This is Step I of the proof of Lemma 8.1; it rests on Theorem 8.2.
--
--   **Formalization Note** The hypotheses are those of Lemma 8.1, inside whose proof the proposition is stated. Every part $E_i$ is a non-empty matching (a partition has non-empty parts, so the parts cannot be padded to inflate $s$).
--
--   Differences from the source:
--   - reading: Proposition 8.3 has no hypotheses of its own; it is stated in the proof of Lemma 8.1 ('Let H and R be 3-graphs satisfying the hypothesis of the lemma', p.31) → the full hypotheses of Lemma 8.1, copied verbatim; reason: these are the standing assumptions of the proof the proposition belongs to
--   - reading: 'for a sufficiently large constant C' (and integer n) → ∃ C₀, ∀ C ≥ C₀ (then ∃ n₀, ∀ n ≥ n₀ where the source says n is large); reason: the standard reading, and the way the paper applies these results ('Let C be a constant larger than all the previous constants', p.31)
--   - reading: |S| = n/100 → S.card = n / 100 in ℕ, i.e. ⌊n/100⌋; reason: the real equation is unsatisfiable unless 100 ∣ n, which would make the lemma vacuous for most n, while the paper applies it for every n (Prop 9.5, p.50)
--   - reading: 'a partition R = E₁ ∪ ⋯ ∪ E_s into matchings' → pairwise disjoint matchings E_i, each non-empty, with union R; reason: parts of a partition are non-empty; this is the stronger reading (empty parts would let s be padded), and the proof's partition from Theorem 8.2 has non-empty colour classes after discarding empty ones
--   - reading: log (base not named) → natural logarithm Real.log; reason: standard convention; paper.md decision 6
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Proposition 8.3, p.33 (hypotheses: Lemma 8.1, p.31)

import Mathlib
import Definitions.Def_HypClass1_K3
import Definitions.Def_HypClass1_deg
import Definitions.Def_HypClass1_maxCodeg
import Definitions.Def_HypClass1_IsMatching
import Definitions.Def_HypClass1_IsPseudorandom3

namespace HypClass1

/-- **Proposition 8.3 (Step I of Stage II: partitioning R into matchings).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Proposition 8.3,
p.33: "There exists a partition R = E₁ ∪ ⋯ ∪ E_s into matchings such that s = (1 ± 1/k²)rn²/2.
Moreover, all but at most s/k of the matchings E_i satisfy |E_i| ≥ n/3 − n/k."

**Formalization Note.** The proposition is stated inside the proof of Lemma 8.1 ("Let H and R be
3-graphs satisfying the hypothesis of the lemma", p.31); its hypotheses are those of Lemma 8.1,
copied verbatim (parameters (17), `S`, `H`, `R`), with `∃ C₀, ∀ C ≥ C₀, ∃ n₀, ∀ n ≥ n₀`. A partition is
a family `E : Fin s → Finset (Finset (Fin n))` of pairwise disjoint non-empty matchings with union `R`
(a partition has non-empty parts, so `s` counts genuine matchings and cannot be padded). `s = (1 ± 1/k²)rn²/2` means `(1 − 1/k²)rn²/2 ≤ s ≤ (1 + 1/k²)rn²/2`. -/
theorem proposition_8_3 :
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ ε δ p q r lam : ℝ, 0 ≤ ε → ε ≤ 1 → 0 ≤ δ → δ ≤ 1 → 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
        0 ≤ r → r ≤ 1 → 0 ≤ lam → lam ≤ 1 → ∀ k : ℕ, 0 < k →
        Real.log n ≤ k → (k : ℝ) ≤ (n : ℝ) ^ (0.01 : ℝ) → ε ≤ 1 / (k : ℝ) ^ 2 →
        C ^ 3 / (k : ℝ) ^ 2 ≤ δ → 0.01 ≤ p →
        (k : ℝ) ^ 7 * Real.log n / n ≤ r → r ≤ 1 / (k : ℝ) ^ 6 →
        C ^ 4 * k * r * Real.log n ^ 3 ≤ q →
        C * Real.log n / n ≤ lam → lam ≤ r / (3 * (k : ℝ) ^ 2) →
        ∀ S : Finset (Fin n), S.card = n / 100 →
        ∀ H R : Finset (Finset (Fin n)), H ⊆ K3 (Fin n) → R ⊆ K3 (Fin n) → Disjoint H R →
        IsPseudorandom3 ε p Finset.univ H → (maxCodeg R : ℝ) ≤ C * r * n →
        (∀ u : Fin n, |(deg H u : ℝ) - p * n ^ 2 / 2| ≤ lam * n ^ 2) →
        (∀ u : Fin n, |(deg R u : ℝ) - r * n ^ 2 / 2| ≤ lam * n ^ 2) →
        ∃ s : ℕ, ∃ E : Fin s → Finset (Finset (Fin n)),
          Finset.univ.biUnion E = R ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
          (∀ i, IsMatching (E i) ∧ (E i).Nonempty) ∧
          (1 - 1 / (k : ℝ) ^ 2) * r * n ^ 2 / 2 ≤ s ∧ (s : ℝ) ≤ (1 + 1 / (k : ℝ) ^ 2) * r * n ^ 2 / 2 ∧
          ((Finset.univ.filter (fun i => ((E i).card : ℝ) < n / 3 - n / k)).card : ℝ) ≤ s / k := by sorry

end HypClass1
