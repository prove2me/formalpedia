-- Prove2me | Theorems.Thm_MWCSherali_lemma_3_1
-- name    : MWCSherali.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:12:56.603191+00:00
-- url     : https://prove2.me/theorems/65ea254a-2670-4d0f-9d49-b71af5215cab
-- title:
--   Lemma 3.1 — total flow in the Flow LP
-- statement:
--   Let $n\ge1$. In any feasible solution of (Flow-LP),
--
--   $$\sum_{a,x,i}f_{a,x,i}=kn,$$
--
--   the sum running over the variables of the LP: commodities $a\in[k]$, points $x\in\Delta_{k,n}$ with $a\in\operatorname{supp}(x)$, and directions $i\neq a$. Each commodity carries one unit of flow over $n$ steps.
--
--   Differences from the source:
--   - encoding: n a positive integer (p.4) → hypothesis 0 < n; reason: Δ_{k,n} is defined only for positive n
--   - encoding: points x ∈ Δ_{k,n} with coordinates in (1/n)ℤ, 1-based indices → integer coordinates y = n x (Grid k n), 0-based indices; reason: Lean convention; the same points
--   - encoding: flow variables f_{a,x,i} for a ∈ supp(x), i ≠ a → a total function f with f ≥ 0 everywhere; the sum restricted to x_a > 0, i ≠ a; reason: values outside the variables enter no other constraint
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 3.1, p.23

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_FlowFeasible

namespace MWCSherali

/-- **Lemma 3.1 (total flow).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 3.1, p.23: "In any feasible solution to
(Flow-LP) we have `∑_{a,x,i} f_{a,x,i} = kn`."

The sum runs over the variables of (Flow-LP): commodities `a`, points `x ∈ Δ_{k,n}` with
`a ∈ supp(x)`, and directions `i ≠ a`.

**Formalization Note.** `f a x i` with `x_a = 0` or `i = a` is not a variable and is excluded
from the sum. The paper's `n` is a positive integer. -/
theorem lemma_3_1 (k n : ℕ) (hn : 0 < n) (f : Fin k → Grid k n → Fin k → ℝ)
    (b : Grid k n → Fin k → ℝ) (h : FlowFeasible k n f b) :
    ∑ a, ∑ x ∈ Finset.univ.filter (fun x : Grid k n => 0 < x.1 a),
        ∑ i ∈ Finset.univ.filter (· ≠ a), f a x i = (k * n : ℝ) := by sorry

end MWCSherali
