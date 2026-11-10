-- Prove2me | Theorems.Thm_MovementSorting_Exponent_lemma_2_5
-- name    : MovementSorting.Exponent.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:01:23.618026+00:00
-- url     : https://prove2.me/theorems/2993aa7d-f565-449b-9e51-d6b942ed654c
-- title:
--   Lemma 2.5 — the round-balance equations have a unique solution, giving β^{(d)}_r
-- statement:
--   Let $d \ge 1$, $r \ge 2$, $D = 2d$ and $q = (D-1)/D$. The system (2.1)–(2.3) in the unknowns $\beta, a_0,\dots,a_{r-2}$ has the solution $\beta = 1 + (1-q)/(1-q^r)$, $a_j = (q^{j+1}-q^r)/(1-q^r)$ ($0 \le j \le r-2$), and every solution equals it; this $\beta$ equals $\beta^{(d)}_r = 1 + D^{r-1}/(D^r-(D-1)^r)$; $1 > a_0 > a_1 > \dots > a_{r-2} > 0$, so the $a_j$ define a schedule; and $a_0 = 1 - \delta$ with $\delta = \beta^{(d)}_r - 1 = (1-q)/(1-q^r)$.
--
--   Differences from the source:
--   - encoding: unknowns a_0, …, a_{r−2} → a : ℕ → ℝ, the equations constrain a_0, …, a_{r−2} and uniqueness is asserted for those entries only; reason: a finite tuple written as a sequence whose other entries are irrelevant
--   - encoding: "We write δ = β^{(d)}_r − 1 = (1−q)/(1−q^r), so a_0 = 1 − δ" → schedExp d r 0 = 1 − (beta d r − 1), with δ = (1−q)/(1−q^r) already given by the third conjunct; reason: δ is notation; the claim a_0 = 1 − δ is kept
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Lemma 2.5, p. 9

import Definitions.Def_MovementSorting_Exponent_Beta

set_option autoImplicit false

namespace MovementSorting.Exponent

/-- Lemma 2.5 (p. 9): for `r ≥ 2` and `q = (D-1)/D`, Equations (2.1)–(2.3) have the unique
solution `β = 1 + (1-q)/(1-q^r)`, `a_j = (q^{j+1} - q^r)/(1 - q^r)` (`0 ≤ j ≤ r-2`); this `β` is
`β^{(d)}_r`; `1 > a_0 > a_1 > ⋯ > a_{r-2} > 0`; and `a_0 = 1 - (β - 1)`. -/
theorem lemma_2_5 (d r : ℕ) (hd : 1 ≤ d) (hr : 2 ≤ r) :
    IsScheduleSolution d r (1 + (1 - qRatio d) / (1 - qRatio d ^ r)) (schedExp d r) ∧
    (∀ (β : ℝ) (a : ℕ → ℝ), IsScheduleSolution d r β a →
      β = 1 + (1 - qRatio d) / (1 - qRatio d ^ r) ∧ ∀ j : ℕ, j ≤ r - 2 → a j = schedExp d r j) ∧
    beta d r = 1 + (1 - qRatio d) / (1 - qRatio d ^ r) ∧
    schedExp d r 0 < 1 ∧
    (∀ j : ℕ, j + 1 ≤ r - 2 → schedExp d r (j + 1) < schedExp d r j) ∧
    0 < schedExp d r (r - 2) ∧
    schedExp d r 0 = 1 - (beta d r - 1) := by sorry

end MovementSorting.Exponent
