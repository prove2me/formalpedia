-- Prove2me | Theorems.Thm_GaugeFunctor_holF_full
-- name    : GaugeFunctor.holF_full
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T09:55:13.63812+00:00
-- url     : https://prove2.me/theorems/6ec555fc-2b16-4ce2-9d2e-622c0c41d73b
-- title:
--   The holonomy functor is full
-- statement:
--   Setting: $X$ is a finite directed graph with vertex set $V=\{0,\dots,n_V-1\}$, edge set $E$ and maps $\mathrm{src},\mathrm{tgt}:E\to V$; a walk may use edges in either direction, and $X$ is *connected from* $x$ if every vertex is reached by a walk from $x$. $G$ is any group. A connection is $A:E\to G$; its holonomy $\mathrm{hol}_A(w)$ along a walk $w$ is the ordered product of $A(e)$ on forward steps and $A(e)^{-1}$ on backward steps. A gauge transformation $g:V\to G$ acts by $(g\cdot A)(e)=g(\mathrm{src}\,e)\,A(e)\,g(\mathrm{tgt}\,e)^{-1}$. $\mathsf{Pot}_G(X)$ is the category whose objects are connections and whose arrows $A\to B$ are gauge transformations $g$ with $g\cdot A=B$. $\mathsf{Hol}_x$ is the category of holonomy maps at $x$ (assignments $H$ of group elements to walks, multiplicative on loops at $x$ and unchanged by inserting a backtrack into a loop at $x$), with arrows $h:H\to H'$ the elements $h\in G$ such that $H'(\gamma)=h\,H(\gamma)\,h^{-1}$ for every loop $\gamma$ at $x$. The holonomy functor $\mathrm{hol}_x:\mathsf{Pot}_G(X)\to\mathsf{Hol}_x$ sends $A\mapsto\mathrm{hol}_A$ and $g\mapsto g(x)$.
--
--   **Statement.** If $X$ is connected from $x$, then $\mathrm{hol}_x$ is full: whenever $h\in G$ satisfies $\mathrm{hol}_B(\gamma)=h\,\mathrm{hol}_A(\gamma)\,h^{-1}$ for every loop $\gamma$ at $x$, there is a gauge transformation $g$ with $g\cdot A=B$ and $g(x)=h$.
-- source:
--   S. Rosenstock, J. O. Weatherall, A categorical equivalence between generalized holonomy maps on a connected manifold and principal connections on bundles over that manifold, J. Math. Phys. 57 (2016) 102902, https://arxiv.org/abs/1504.02401, Theorem 2 and p. 3 (Barrett representation theorem). Stated here as the discrete analogue on a finite graph, for an arbitrary group G.

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

/-- On a graph connected from `x`, if `h : G` conjugates the holonomies at `x` of `A` into
those of `B`, some gauge transformation `g` with `g x = h` carries `A` to `B`: the holonomy
functor is full. -/
theorem holF_full (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) : (holF X G x).Full := by sorry

end GaugeFunctor
