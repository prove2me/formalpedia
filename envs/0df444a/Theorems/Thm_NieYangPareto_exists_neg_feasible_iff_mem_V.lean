-- Prove2me | Theorems.Thm_NieYangPareto_exists_neg_feasible_iff_mem_V
-- name    : NieYangPareto.exists_neg_feasible_iff_mem_V
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:49.703988+00:00
-- url     : https://prove2.me/theorems/d5069405-7dc2-4305-8897-2d7ef30227b6
-- title:
--   §3.2 before (3.4) — a feasible $t<0$ in (3.3) exists iff $v\in\mathcal V$
-- statement:
--   Let $m\ge1$ and $v\in\mathbb R^m$. The program (3.3) has a feasible point $(t,y)$ with $t<0$ if and only if $v\in\mathcal V$; that is, if and only if there is $y\in\mathscr R_d(K)$ with $y_0=1$ and
--
--   $$
--   v_i>\langle f_i,y\rangle,\quad i=1,\dots,m .
--   $$
--
--   This is where the set $\mathcal V$ comes from: it is the sign condition on the dual program, with the closure removed and the mass normalized.
--
--   Differences from the source:
--   - encoding: disjoint finite label sets ℰ, ℐ → two finite types E, I (`[Finite E] [Finite I]`), each with its own constraint family; reason: separate types encode disjointness; the same instances
--   - encoding: tms y ∈ ℝ^{ℕⁿ_d} → y : TmsIndex n d → ℝ, on the finite subtype {α : Fin n →₀ ℕ // α.degree ≤ d}, with the product topology; reason: the same finite-dimensional Euclidean space
--   - encoding: y = ∫[x]_d dμ in (2.2) → each monomial of degree ≤ d is μ-integrable and y_α = ∫x^α dμ; reason: this is what the page's equation means; it stops the junk value ∫ = 0 from entering
--   - reading: (3.2), (3.3) introduced "for given v ∈ f(K)" (p.8) → v ranges over all of ℝ^m; reason: the proof of Theorem 3.2 (p.9) applies them to arbitrary v
--   - reading: m unbounded below ("several objective functions") → hypothesis 0 < m; reason: at m = 0 the equality of (3.3) reads 1 = 0 and eᵀw = 1 reads 0 = 1, so the programs are meaningless there
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, §3.2 before (3.4), p.8

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_MOP_V
import Definitions.Def_NieYangPareto_Programs

namespace NieYangPareto

/-- **A feasible `t < 0` in (3.3) exists iff `v ∈ 𝒱`.** Nie–Yang, arXiv:2108.04336v2, §3.2 before
(3.4), p.8: the existence of `t < 0` in (3.3) is equivalent to `v_i > ⟨f_i, y⟩`, `i = 1, …, m`,
`y₀ = 1`, `y ∈ ℛ_d(K)`.

**Formalization Note** `v` is arbitrary. `0 < m` is needed: for `m = 0` and `K` nonempty, (3.3) is
infeasible while `𝒱 = ℝ⁰`. -/
theorem exists_neg_feasible_iff_mem_V {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I)
    (hm : 0 < m) (v : Fin m → ℝ) :
    (∃ q ∈ P.feasible33 v, q.1 < 0) ↔ v ∈ P.V := by sorry

end NieYangPareto
