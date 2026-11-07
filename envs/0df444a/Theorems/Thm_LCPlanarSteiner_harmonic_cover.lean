-- Prove2me | Theorems.Thm_LCPlanarSteiner_harmonic_cover
-- name    : LCPlanarSteiner.harmonic_cover
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:03:31.344779+00:00
-- url     : https://prove2.me/theorems/4f49ebd9-cf9e-4661-99a7-ff1344666c73
-- title:
--   Proof of Theorem 1.2 (counting step) — harmonic cover: $\sum_j a_j/r_j \le H_q \le D_q$
-- statement:
--   The forest algorithm repeatedly serves a nonempty set of the remaining pairs. Let $q \ge 1$ and let $q = r_1 > r_2 > \cdots > r_J \ge 1$ be the numbers of remaining pairs before the iterations, $r_{J+1} = 0$, so that iteration $j$ removes $a_j = r_j - r_{j+1}$ of the $r_j$ identities.
--
--   **Harmonic cover (proof of Theorem 1.2, p.16).**
--   $$
--   \sum_{j} \frac{a_j}{r_j} \le H_q \le D_q,\qquad H_q = \sum_{i=1}^{q} \frac1i,\quad D_q = 1 + \lceil \log_2 q \rceil .
--   $$
--   Consequently, if iteration $j$ costs at most $a_j K / r_j$ for a constant $K \ge 0$ (a density bound $K/r_j$ per removed pair), the total cost is at most $K D_q$.
--
--   With $K = 79872\, C_{NE} D_q^6 \mathrm{OPT}^F_h/\varepsilon^2$ from Lemmas 4.5 and 4.6 this gives the cost bound of Theorem 1.2.
--
--   Differences from the source:
--   - reading: the proof of Theorem 1.2 at p.16, which also composes Lemmas 4.5 and 4.6 into the density 79872C_NE D_r^6/(ε²r)·OPT^F_h → the counting step only: Σ_j a_j/r_j ≤ H_q ≤ D_q and its cost corollary with an abstract density constant K; reason: the composed density is the conjunction of the milestones Lemma 4.5 and Lemma 4.6; this item is marked as the counting step in its title
--   - encoding: iterations j removing a_j of r_j identities; H_q = Σ_{i=1}^q 1/i → a strictly decreasing list r_1 = q > r_2 > ⋯ > r_J ≥ 1 with r_{J+1} = 0 and a_j = r_j − r_{j+1}; Mathlib's harmonic q; reason: Lean convention, same statement
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Proof of Theorem 1.2, p.16

import Mathlib
import Definitions.Def_LCPlanarSteiner_Dlog

namespace LCPlanarSteiner

/-- **Proof of Theorem 1.2: the harmonic cover sum.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), proof of Theorem 1.2, p.16: "With r pairs remaining, lemmas 4.5 and 4.6 give density at most
79872C_NE D_r^6/(ε²r) · OPT^F_h. The full strict optimum upper-bounds every residual optimum. If
iteration j removes a_j of r_j identities, then Σ_j a_j/r_j ≤ H_q ≤ D_q, where H_q = Σ_{i=1}^q 1/i.
Thus c(F) ≤ 79872C_NE D_q^7/ε² · OPT^F_h."

Let `q ≥ 1` and let `q = r₁ > r₂ > ⋯ > r_J ≥ 1` be the numbers of remaining pairs before the
iterations (`r_{J+1} = 0`), so iteration `j` removes `a_j = r_j − r_{j+1}` identities. Then
1. `Σ_j a_j/r_j ≤ H_q = Σ_{i=1}^q 1/i`;
2. `H_q ≤ D_q = 1 + ⌈log₂ q⌉`;
3. consequently, if iteration `j` costs at most `a_j · K/r_j` (a density bound `K/r_j` per removed
   pair) with `K ≥ 0`, the total cost is at most `K · D_q`.

**Formalization Note.** The sequence is the list `rs = [r₁, …, r_J]` (strictly decreasing, positive,
first entry `q`); `rs.getD (j+1) 0` is `r_{j+1}` with `r_{J+1} = 0`. `H_q` is Mathlib's `harmonic q`. -/
theorem harmonic_cover (q : ℕ) (hq : 1 ≤ q) (rs : List ℕ) (hhead : rs.head? = some q)
    (hdec : rs.IsChain (· > ·)) (hpos : ∀ r ∈ rs, 0 < r) :
    (∑ j ∈ Finset.range rs.length,
        ((rs.getD j 0 - rs.getD (j + 1) 0 : ℕ) : ℚ) / rs.getD j 0) ≤ harmonic q ∧
    harmonic q ≤ (Dlog q : ℚ) ∧
    ∀ (K : ℚ) (c : ℕ → ℚ), 0 ≤ K →
      (∀ j < rs.length, c j ≤ ((rs.getD j 0 - rs.getD (j + 1) 0 : ℕ) : ℚ) * K / rs.getD j 0) →
      ∑ j ∈ Finset.range rs.length, c j ≤ K * Dlog q := by sorry

end LCPlanarSteiner
