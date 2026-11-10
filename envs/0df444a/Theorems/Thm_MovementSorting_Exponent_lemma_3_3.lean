-- Prove2me | Theorems.Thm_MovementSorting_Exponent_lemma_3_3
-- name    : MovementSorting.Exponent.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:02:12.795094+00:00
-- url     : https://prove2.me/theorems/2726edd0-4be1-4562-ab2b-a6db187c228f
-- title:
--   Lemma 3.3 — on the uniform input, half of the co-blocked cells are isolated at radius Θ_d((n/b)^{1/D})
-- statement:
--   Fix $d \ge 1$. There are constants $0 < c_1 \le c_2$ depending only on $d$ such that for every $m \ge 2$ ($n = m^d$) and every integer scale $2 \le b \le n$ there is a radius $\rho$ with $c_1 (n/b)^{1/D} \le \rho \le c_2 (n/b)^{1/D}$ such that, with probability at least $7/8$ over the uniform input, at least half of the cells $w \in C_b$ satisfy $\mathrm{dist}(w, C_b\setminus\{w\}) > \rho$ (i.e. every other cell of $C_b$ is farther than $\rho$ from $w$).
--
--   Differences from the source:
--   - encoding: ρ = Θ_d((n/b)^{1/D}) → ∃ c₁ c₂ (0 < c₁ ≤ c₂, depending on d only) chosen before m and b, and for each m, b a ρ in [c₁(n/b)^{1/D}, c₂(n/b)^{1/D}]; reason: the Θ_d notation of p. 8 made explicit
--   - encoding: "integer scale b ≥ 2" with m ≥ 2 → b : ℕ with 2 ≤ b ≤ m^d, and 2 ≤ m; reason: a scale satisfies 1 ≤ b ≤ n (Definition 2.4), and Definition 2.1 fixes m ≥ 2
--   - encoding: a cell is an unordered pair {x, y} of distinct positions; C_b the cells co-blocked at scale b; blocks {(i−1)b+1,…,ib} ∩ [n] → Cell = Sym2 (Pos d m); coBlocked π b = non-diagonal s(x,y) with π x / b = π y / b (0-based ranks and labels); reason: same cells and same blocks after the 0-based shift
--   - encoding: probability over the uniform input → prob d m E = (PMF.uniformOfFintype (Input d m)).toOuterMeasure {π | E π}; reason: the uniform distribution on the n! bijections
--   - encoding: at least half of the cells w ∈ C_b satisfy dist(w, C_b ∖ {w}) > ρ, with dist(w, ∅) = +∞ → |C_b| ≤ 2·#{w ∈ C_b : ∀ w′ ∈ C_b, w′ ≠ w → ρ < dist w w′}; reason: the vacuous ∀ realizes dist(w, ∅) = +∞
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Lemma 3.3, p. 10

import Definitions.Def_MovementSorting_Exponent_Geometry

set_option autoImplicit false

open scoped ENNReal

namespace MovementSorting.Exponent

/-- Lemma 3.3 (p. 10): for every integer scale `2 ≤ b ≤ n` there is a radius
`ρ = Θ_d((n/b)^{1/D})` such that, with probability at least `7/8` over the uniform input, at least
half of the cells `w ∈ C_b` satisfy `dist(w, C_b ∖ {w}) > ρ`. -/
theorem lemma_3_3 :
    ∀ d : ℕ, 1 ≤ d → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∀ m : ℕ, 2 ≤ m → ∀ b : ℕ, 2 ≤ b → b ≤ m ^ d →
        ∃ ρ : ℝ, c₁ * (nR d m / b) ^ (1 / (2 * d : ℝ)) ≤ ρ ∧
          ρ ≤ c₂ * (nR d m / b) ^ (1 / (2 * d : ℝ)) ∧
          (7 / 8 : ℝ≥0∞) ≤ prob d m (fun π =>
            (coBlocked π b).card ≤ 2 * ((coBlocked π b).filter (fun w =>
              ∀ w' ∈ coBlocked π b, w' ≠ w → ρ < (cellDist w w' : ℝ))).card) := by sorry

end MovementSorting.Exponent
