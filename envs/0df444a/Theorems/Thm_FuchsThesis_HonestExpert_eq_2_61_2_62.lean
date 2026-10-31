-- Prove2me | Theorems.Thm_FuchsThesis_HonestExpert_eq_2_61_2_62
-- name    : FuchsThesis.HonestExpert.eq_2_61_2_62
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:33.681684+00:00
-- url     : https://prove2.me/theorems/30b74775-3e8f-43c5-bb28-6c3b9acb2f67
-- title:
--   (2.61)–(2.62) — the difference-quotient sandwich (corrected: for $q<p$; reversed for $p<q$)
-- statement:
--   Let $n \ge 3$, let $F_1, \dots, F_n$ keep the expert honest, let $i \ne j$ be two outcomes and let $0 < p < r$, $0 < q < r$, $r < 1$. Write
--
--   $$D_j = \frac{F_j(r - q) - F_j(r - p)}{(r - q) - (r - p)}, \qquad D_i = \frac{F_i(p) - F_i(q)}{p - q}$$
--
--   for the difference quotients of $F_j$ between $r-q$ and $r-p$ and of $F_i$ between $q$ and $p$. Then:
--
--   1. if $q < p$:
--   $$\frac{r - p}{p}\, D_j \;\le\; D_i \;\le\; \frac{r - q}{q}\, D_j ;$$
--   2. if $p < q$:
--   $$\frac{r - q}{q}\, D_j \;\le\; D_i \;\le\; \frac{r - p}{p}\, D_j .$$
--
--   Clause 1 is (2.61)–(2.62) as printed. The sandwich pins the difference quotient of $F_i$ at $p$ between multiples of the difference quotient of $F_j$ at $r - p$; letting $q \to p$ ("Pinching Theorem", (2.63)–(2.65)) transfers differentiability from $F_j$ to $F_i$, which is (2.66).
--
--   Differences from the source:
--   - correction: (2.61)–(2.62) for every q ≠ p → (2.61)–(2.62) for q < p, and the reversed inequalities for p < q; reason: the page obtains them by dividing (2.59)–(2.60) by p − q, which reverses them when p < q. Counterexample to the printed form (all assumptions met): F_k = ln (honest by Theorem 2.3 with α = 1), r = 0.9, p = 0.1, q = 0.2 gives ((r − p)/p) D_j = 8·ln(8/7)/0.1 ≈ 10.68 > D_i = ln 2/0.1 ≈ 6.93, so (2.61) fails
--   - generalization: the outcomes 1 and 2 → any two distinct outcomes i ≠ j; reason: p.24 runs the same argument for the pair (1, k); i = 1, j = 2 gives the page's case
--   - reading: (2.45) for all n-point distributions → (2.45) for all strictly positive n-point distributions; reason: the positivity reading of Theorem 2.3; the hypothesis is weaker
--   - encoding: outcomes 1, …, n → Fin n; reason: Lean indexing
--   - encoding: real payoffs F_k defined on [0, 1] → real functions F_k defined on all of ℝ; reason: only values on (0, 1) enter (the coordinates of strictly positive distributions for n ≥ 3); any F_k on [0, 1] extends to ℝ and the extension changes no clause
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.3.1, eqs. (2.59)–(2.62), p.22 (PDF p.31)

import Mathlib
import Definitions.Def_FuchsThesis_HonestExpert_KeepsHonest

namespace FuchsThesis.HonestExpert

/-- **(2.61)–(2.62): the difference-quotient sandwich (corrected: `q < p`; reversed for `p < q`).**
Fuchs, *Distinguishability and Accessible Information in Quantum Theory*, arXiv:quant-ph/9601020v1,
§2.3.1, eqs. (2.59)–(2.62), p.22 (PDF p.31): dividing (2.59)–(2.60) through by `p − q`,
`((r − p)/p) · (F₂(r − q) − F₂(r − p))/((r − q) − (r − p)) ≤ (F₁(p) − F₁(q))/(p − q)` (2.61) and
`(F₁(p) − F₁(q))/(p − q) ≤ ((r − q)/q) · (F₂(r − q) − F₂(r − p))/((r − q) − (r − p))` (2.62).

For `n ≥ 3`, payoffs `F` keeping the expert honest, outcomes `i ≠ j` (the page's `1, 2`) and
`0 < p, q < r < 1`, write `D₂ = (F_j(r − q) − F_j(r − p))/((r − q) − (r − p))` and
`D₁ = (F_i(p) − F_i(q))/(p − q)`. Then
1. if `q < p`: `((r − p)/p) D₂ ≤ D₁ ≤ ((r − q)/q) D₂` ((2.61) and (2.62) as printed);
2. if `p < q`: `((r − q)/q) D₂ ≤ D₁ ≤ ((r − p)/p) D₂` (the inequalities reversed).

**Correction.** Division by `p − q < 0` reverses (2.59)–(2.60), so the printed (2.61)–(2.62) hold
only for `q < p`. Counterexample to the printed form for `p < q`: `F_k = ln` (honest by Theorem 2.3
with `α = 1`), `r = 0.9`, `p = 0.1`, `q = 0.2`: `((r − p)/p) D₂ = 8 ln(8/7)/0.1 ≈ 10.68` while
`D₁ = ln 2/0.1 ≈ 6.93`, so (2.61) fails. Clause 2 is clause 1 with `p` and `q` interchanged. -/
theorem eq_2_61_2_62 {n : ℕ} (hn : 3 ≤ n) {F : Fin n → ℝ → ℝ} (hF : KeepsHonest F)
    {i j : Fin n} (hij : i ≠ j) {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hpr : p < r)
    (hqr : q < r) (hr : r < 1) :
    (q < p →
      (r - p) / p * ((F j (r - q) - F j (r - p)) / ((r - q) - (r - p))) ≤
          (F i p - F i q) / (p - q) ∧
        (F i p - F i q) / (p - q) ≤
          (r - q) / q * ((F j (r - q) - F j (r - p)) / ((r - q) - (r - p)))) ∧
    (p < q →
      (r - q) / q * ((F j (r - q) - F j (r - p)) / ((r - q) - (r - p))) ≤
          (F i p - F i q) / (p - q) ∧
        (F i p - F i q) / (p - q) ≤
          (r - p) / p * ((F j (r - q) - F j (r - p)) / ((r - q) - (r - p)))) := by sorry

end FuchsThesis.HonestExpert
