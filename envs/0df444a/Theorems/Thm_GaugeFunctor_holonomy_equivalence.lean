-- Prove2me | Theorems.Thm_GaugeFunctor_holonomy_equivalence
-- name    : GaugeFunctor.holonomy_equivalence
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T09:59:30.003455+00:00
-- url     : https://prove2.me/theorems/156ef29a-829a-49d5-b0c1-9407c5fb08fb
-- title:
--   The holonomy functor is an equivalence of categories
-- statement:
--   Setting: $X$ is a finite directed graph with vertex set $V=\{0,\dots,n_V-1\}$, edge set $E$ and maps $\mathrm{src},\mathrm{tgt}:E\to V$; a walk may use edges in either direction, and $X$ is *connected from* $x$ if every vertex is reached by a walk from $x$. $G$ is any group. A connection is $A:E\to G$; its holonomy $\mathrm{hol}_A(w)$ along a walk $w$ is the ordered product of $A(e)$ on forward steps and $A(e)^{-1}$ on backward steps. A gauge transformation $g:V\to G$ acts by $(g\cdot A)(e)=g(\mathrm{src}\,e)\,A(e)\,g(\mathrm{tgt}\,e)^{-1}$. $\mathsf{Pot}_G(X)$ is the category whose objects are connections and whose arrows $A\to B$ are gauge transformations $g$ with $g\cdot A=B$. $\mathsf{Hol}_x$ is the category of holonomy maps at $x$ (assignments $H$ of group elements to walks, multiplicative on loops at $x$ and unchanged by inserting a backtrack into a loop at $x$), with arrows $h:H\to H'$ the elements $h\in G$ such that $H'(\gamma)=h\,H(\gamma)\,h^{-1}$ for every loop $\gamma$ at $x$. The holonomy functor $\mathrm{hol}_x:\mathsf{Pot}_G(X)\to\mathsf{Hol}_x$ sends $A\mapsto\mathrm{hol}_A$ and $g\mapsto g(x)$.
--
--   **Statement.** If $X$ is connected from $x$, then $\mathrm{hol}_x:\mathsf{Pot}_G(X)\to\mathsf{Hol}_x$ is full, faithful and essentially surjective, i.e. an equivalence of categories.
-- source:
--   S. Rosenstock, J. O. Weatherall, A categorical equivalence between generalized holonomy maps on a connected manifold and principal connections on bundles over that manifold, J. Math. Phys. 57 (2016) 102902, https://arxiv.org/abs/1504.02401, Theorem 2 (fixed base point). Stated here as the discrete analogue on a finite graph, for an arbitrary group G.

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

/-- Discrete Rosenstock–Weatherall theorem: on a graph connected from the base vertex `x`, the
holonomy functor from connections-with-gauge-arrows to holonomy maps at `x` is full, faithful
and essentially surjective, i.e. an equivalence of categories. -/
theorem holonomy_equivalence (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) :
    (holF X G x).Full ∧ (holF X G x).Faithful ∧ (holF X G x).EssSurj := by sorry

end GaugeFunctor
