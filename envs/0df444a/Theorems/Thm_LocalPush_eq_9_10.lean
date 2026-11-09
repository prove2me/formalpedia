-- Prove2me | Theorems.Thm_LocalPush_eq_9_10
-- name    : LocalPush.eq_9_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:07.285901+00:00
-- url     : https://prove2.me/theorems/2dcd45fa-8f44-4ff0-b2fb-fd6bbd9c4b50
-- title:
--   Eqs. (9)–(10) — mass identity $\mathbf 1^\top Dx+\mathbf 1^\top r(x)=1$ and the residue outside the support
-- statement:
--   Let $G$ be a finite simple graph without isolated nodes, $s\in V$, $\alpha\in(0,1)$, and $r(x)=e_s-\frac1\alpha L_\alpha x$. Then:
--
--   1. for every $x\in\mathbb R^V$,
--   $$\sum_v d(v)x(v)+\sum_v r(x)(v)=1;\tag{9}$$
--   2. if $x$ vanishes outside $S$ and $s\in S$, then
--   $$r(x)(v)=\frac{1-\alpha}{\alpha}\sum_{u\in N(v)\cap S}x(u)\qquad\forall v\in V\setminus S;\tag{10}$$
--   3. under the same hypotheses, $r(x)(v)=0$ for every $v\notin S\cup\partial S$.
--
--   The mass identity bounds the volume of active sets, and (10) is how the algorithm computes boundary residues from the solver output.
--
--   Differences from the source: none.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §5.1, eqs. (9), (10), p.16 (PDF p.16)

import Mathlib
import Definitions.Def_LocalPush_ResidueSystem

open Finset Matrix

namespace LocalPush

/-- **Eqs. (9) and (10): the mass identity and the residue outside the support.**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §5.1, p.16 (PDF p.16).

"For any x ∈ ℝ^V, multiplying Equation (8) by 1ᵀ gives 1ᵀDx + 1ᵀr(x) = 1. (9) Additionally, by inspecting
Equation (8) entrywise, we have that, if supp(x) ⊆ S and s ∈ S, then r(x)(v) = ((1−α)/α) ∑_{u∈N(v)∩S} x(u),
∀ v ∈ V ∖ S. (10) In particular, r(x)(v) = 0 for every v ∉ S ∪ ∂S."

Here `r(x) = e_s − (1/α)L_α x` (eq. (8)), on a simple graph without isolated nodes with `α ∈ (0, 1)`:
1. `∑_v d(v)x(v) + ∑_v r(x)(v) = 1` for every `x`;
2. if `x` vanishes outside `S` and `s ∈ S`, then `r(x)(v) = ((1−α)/α)∑_{u∈N(v)∩S} x(u)` for every `v ∉ S`;
3. under the same hypotheses, `r(x)(v) = 0` for every `v ∉ S ∪ ∂S`. -/
theorem eq_9_10 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ x : V → ℝ, ∑ v, deg G v * x v + ∑ v, resid G α s x v = 1) ∧
    (∀ (x : V → ℝ) (S : Finset V), (∀ v ∉ S, x v = 0) → s ∈ S →
      ∀ v ∉ S, resid G α s x v = (1 - α) / α * ∑ u ∈ S.filter (G.Adj v), x u) ∧
    (∀ (x : V → ℝ) (S : Finset V), (∀ v ∉ S, x v = 0) → s ∈ S →
      ∀ v, v ∉ S → v ∉ bdry G S → resid G α s x v = 0) := by sorry

end LocalPush
