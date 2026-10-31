-- Prove2me | Theorems.Thm_LeastMajorized_lemma_2_extreme_points_greedy
-- name    : LeastMajorized.lemma_2_extreme_points_greedy
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:50.469616+00:00
-- url     : https://prove2.me/theorems/34612c09-b11c-4476-91c1-c1dd50d9e21f
-- title:
--   Lemma 2 — extreme points of a base polyhedron are greedy vectors
-- statement:
--   Let $f:2^N\to\mathbb R$ be submodular (with $f(\emptyset)=0$) and let $z$ be an extreme point of the base polyhedron $B(f)$. Then there is a permutation $\pi$ of $N=\{1,\dots,n\}$ such that
--
--   $$
--   z_{\pi(1)}=f(\{\pi(1)\}),\qquad z_{\pi(k)}=f(\{\pi(1),\dots,\pi(k)\})-f(\{\pi(1),\dots,\pi(k-1)\})\quad (k=2,\dots,n).
--   $$
--
--   This is the classical description of the vertices of a base polyhedron (Theorem 3.4 of Fujishige and Tomizawa, J. Oper. Res. Soc. Japan, 1983, as cited by the paper). It is used in Lemma 15 to show that $B(f)\subseteq\mathrm{co}(C)$.
--
--   Differences from the source:
--   - reading: "extreme point of a (integral) base polyhedron defined by a (integral) submodular function" → extreme points of B(f) for real-valued submodular f; reason: the parenthetical integral case is the special case of an integer-valued f, which the real statement covers; for integral f the vertices of co(B^ℤ(f)) are extreme points of B(f)
--   - encoding: two formulas, for k = 1 and for k ∈ {2, …, n} → one formula z(π k) = f(π[{j ≤ k}]) − f(π[{j < k}]) for k : Fin n; reason: at k = 1 (index 0) the second set is ∅ and f(∅) = 0 is part of submodularity, so the two printed cases are exactly the one formula
--   - encoding: N = {1, …, n}, permutations of N, f : 2^N → ℝⁿ (typo) → Fin n (0-based), Equiv.Perm (Fin n), f : Finset (Fin n) → ℝ; reason: Lean convention; same instances; the printed codomain ℝⁿ is a typo for ℝ
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, Lemma 2, p.5

import Mathlib
import Definitions.Def_LeastMajorized_IsSubmodular
import Definitions.Def_LeastMajorized_basePolyhedron

namespace LeastMajorized

/-- **Lemma 2**, Schoot Uiterkamp, arXiv:2201.06596v2, p.5 (the paper cites Theorem 3.4 of
Fujishige and Tomizawa, *A note on submodular functions on distributive lattices*, J. Oper. Res.
Soc. Japan 26(4), 1983): "For each extreme point `z` of a (integral) base
polyhedron defined by a (integral) submodular function `f`, there exists a permutation `π` of `N`
such that `z_{π(1)} = f({π(1)})` and `z_{π(k)} = f({π(1), …, π(k)}) − f({π(1), …, π(k − 1)})`
for each `k ∈ {2, …, n}`."

**Formalization Note** The real statement is formalized; the parenthetical integral reading is
the special case of an integer-valued `f`, which it covers. A permutation of `N` is
`Equiv.Perm (Fin n)`, 0-based: for `k : Fin n`, `{π(1), …, π(k)}` is the image under `π` of
`{j | j ≤ k}` and `{π(1), …, π(k − 1)}` the image of `{j | j < k}`. The case `k = 1` of the
paper is `k = 0` here, where the second set is `∅` and `f(∅) = 0` (part of `IsSubmodular`), so
one formula covers both of the paper's cases. Extreme points are Mathlib's
`Set.extremePoints ℝ`. -/
theorem lemma_2_extreme_points_greedy {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hf : IsSubmodular f) (z : Fin n → ℝ) (hz : z ∈ Set.extremePoints ℝ (basePolyhedron f)) :
    ∃ π : Equiv.Perm (Fin n), ∀ k : Fin n,
      z (π k) = f ((Finset.univ.filter (fun j : Fin n => j ≤ k)).image π) -
        f ((Finset.univ.filter (fun j : Fin n => j < k)).image π) := by sorry

end LeastMajorized
