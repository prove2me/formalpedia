-- Prove2me | Theorems.Thm_GaugeFunctor_aharonov_bohm_nonabelian
-- name    : GaugeFunctor.aharonov_bohm_nonabelian
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T09:58:56.440599+00:00
-- url     : https://prove2.me/theorems/2d1dd372-8246-457e-a08e-35f9d461fff0
-- title:
--   Aharonov-Bohm: curvature forgets structure on a circle
-- statement:
--   Setting: $X$ is a finite directed graph with vertex set $V=\{0,\dots,n_V-1\}$, edge set $E$ and maps $\mathrm{src},\mathrm{tgt}:E\to V$; a walk may use edges in either direction, and $X$ is *connected from* $x$ if every vertex is reached by a walk from $x$. $G$ is any group. A connection is $A:E\to G$; its holonomy $\mathrm{hol}_A(w)$ along a walk $w$ is the ordered product of $A(e)$ on forward steps and $A(e)^{-1}$ on backward steps. A gauge transformation $g:V\to G$ acts by $(g\cdot A)(e)=g(\mathrm{src}\,e)\,A(e)\,g(\mathrm{tgt}\,e)^{-1}$. $\mathsf{Pot}_G(X)$ is the category whose objects are connections and whose arrows $A\to B$ are gauge transformations $g$ with $g\cdot A=B$. $\mathsf{Hol}_x$ is the category of holonomy maps at $x$ (assignments $H$ of group elements to walks, multiplicative on loops at $x$ and unchanged by inserting a backtrack into a loop at $x$), with arrows $h:H\to H'$ the elements $h\in G$ such that $H'(\gamma)=h\,H(\gamma)\,h^{-1}$ for every loop $\gamma$ at $x$. The holonomy functor $\mathrm{hol}_x:\mathsf{Pot}_G(X)\to\mathsf{Hol}_x$ sends $A\mapsto\mathrm{hol}_A$ and $g\mapsto g(x)$.
--
--   For a 2-complex $Y$ (a graph with faces, each with a base vertex and a boundary loop there), the curvature functor $\mathrm{curv}_Y$ sends a connection to the family of conjugacy classes of its holonomies around the faces, into the discrete category on such families. Let $\partial\Delta$ be the triangle $0\to1\to2\to0$ with no faces (a circle) and $\Delta$ the same triangle with one face bounded by the loop $0\to1\to2\to0$.
--
--   **Statement.** For every nontrivial group $G$: $\mathrm{curv}_{\partial\Delta}$ is not full, while $\mathrm{curv}_{\Delta}$ is full and essentially surjective but not faithful.
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (arXiv v2 includes the erratum, p. 15), §4, Proposition 1 (p. 8) and fn. 9; J. Nguyen, N. J. Teh, L. Wells, Why surplus structure is not superfluous, Brit. J. Phil. Sci. 71 (2020), https://arxiv.org/abs/1712.01228, Proposition 3.2.1. Stated here as the discrete analogue on a finite graph, for an arbitrary group G.

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

/-- Aharonov–Bohm on a triangle, for any nontrivial group `G` (abelian or not). On the circle
(no faces) the curvature functor is not full: flat connections with different holonomy are
not gauge-equivalent. On the filled triangle it is full and essentially surjective but not
faithful, so it forgets only stuff. -/
theorem aharonov_bohm_nonabelian (G : Type) [Group G] [Nontrivial G] :
    ¬ (curvF G circleC).Full ∧
      (curvF G filledC).Full ∧ (curvF G filledC).EssSurj ∧ ¬ (curvF G filledC).Faithful := by sorry

end GaugeFunctor
