-- Prove2me | Theorems.Thm_OPG37364_lps13_adjacency_eigenspace_invariant
-- name    : OPG37364.lps13_adjacency_eigenspace_invariant
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T15:39:27.539953+00:00
-- url     : https://prove2.me/theorems/24cabfd8-9440-4839-8551-4a6d80508935
-- title:
--   PSL₂ invariance of the fixed-p=13 LPS adjacency eigenspaces
-- statement:
--   Let $q>13$ be prime and choose $i\in\mathbb F_q$ with $i^2=-1$. Let $A$ be the ordinary, unnormalized adjacency operator over $\mathbb C$ of the existing fixed-$p=13$ PGL Cayley graph. For every real number $\mu$, every $g\in\operatorname{PSL}_2(\mathbb F_q)$, and every complex-valued vertex function $f$ satisfying $Af=\mu f$, the left translate
--
--   $$(L_gf)(v)=f(j(g)^{-1}v)$$
--
--   also satisfies $A(L_gf)=\mu L_gf$, where $j$ is the natural inclusion into $\operatorname{PGL}_2(\mathbb F_q)$. Thus every such adjacency eigenspace is preserved by the PSL₂ action and supports the restricted finite-dimensional complex representation in the imported constructor.
--
--   The parameter $\mu$ need not be an eigenvalue: a zero eigenspace is allowed. No connectedness, bipartiteness, regularity, girth or spectral-bound assumption is required for this symmetry argument. In particular, this theorem makes no assertion that the restricted representation is nontrivial.
-- source:
--   Davidoff, Sarnak and Valette, Elementary Number Theory, Group Theory, and Ramanujan Graphs (2003), Example 3.4.2(iii)-(iv) and Definition 3.4.3, printed p. 87; Definition 4.1.1, printed p. 108; Section 4.1, Exercise 4(b), printed p. 112. https://math.bme.hu/~gabor/oktatas/SztoM/DavidoffSarnakValette.pdf . Specialization of the classical left-regular invariance of Cayley adjacency eigenspaces to the previously defined fixed-p=13 PGL graph, restricted along the natural PSL₂→PGL₂ inclusion. No claim of mathematical novelty.

import Definitions.Def_opg37364_lps13_eigenspaces
set_option autoImplicit false

namespace OPG37364

theorem lps13_adjacency_eigenspace_invariant
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q) (μ : ℝ) :
    ∀ g : LPS13ActingGroup q,
      Set.MapsTo (lps13LeftRepresentation g)
        ((lps13AdjacencyEnd hq i).eigenspace (μ : ℂ))
        ((lps13AdjacencyEnd hq i).eigenspace (μ : ℂ)) := by sorry

end OPG37364
