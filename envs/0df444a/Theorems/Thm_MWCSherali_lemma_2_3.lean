-- Prove2me | Theorems.Thm_MWCSherali_lemma_2_3
-- name    : MWCSherali.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:15.196359+00:00
-- url     : https://prove2.me/theorems/718ba781-e1ed-478b-8f47-2c75ae0255bc
-- title:
--   Lemma 2.3 — each edge lies in a unique downward cell
-- statement:
--   Let $n\ge1$. For every edge $e=\{x,y\}\in E_{k,n}$ of the discrete simplex there is exactly one downward cell $D\in D_{k,n}$ with $e\subseteq D$, i.e. exactly one $v\in\Delta_{k,n+1}$ with
--
--   $$x\in D(v)\quad\text{and}\quad y\in D(v).$$
--
--   This lets the vertex-consistency LP measure the probability that an edge is cut in the local distribution of "the" cell $D(e)$ containing it.
--
--   Differences from the source:
--   - encoding: n a positive integer (p.4) → hypothesis 0 < n; reason: Δ_{k,n} is defined only for positive n
--   - encoding: points x ∈ Δ_{k,n} with coordinates in (1/n)ℤ, 1-based indices → integer coordinates y = n x (Grid k n), 0-based indices; reason: Lean convention; the same points
--   - encoding: cells C ∈ D_{k,n} → cells indexed by V ∈ Δ_{k,n+1} (Grid k (n+1)); reason: the paper's one-to-one correspondence D_{k,n} ↔ Δ_{k,n+1} (p.15)
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 2.3, p.15

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_edges
import Definitions.Def_MWCSherali_cell

namespace MWCSherali

/-- **Lemma 2.3 (each edge lies in a unique downward cell).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 2.3, p.15:
"For every `e ∈ E_{k,n}`, there exists a unique `D ∈ D_{k,n}` such that `e ⊆ D`."

**Formalization Note.** Cells are indexed by `V : Grid k (n+1)` (the correspondence
`D_{k,n} ↔ Δ_{k,n+1}` is a bijection, p.15), so uniqueness of the cell is uniqueness of `V`. The
paper's `n` is a positive integer. -/
theorem lemma_2_3 (k n : ℕ) (hn : 0 < n) (x y : Grid k n) (he : s(x, y) ∈ edges k n) :
    ∃! V : Grid k (n + 1), x ∈ cell V ∧ y ∈ cell V := by sorry

end MWCSherali
