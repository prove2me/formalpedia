-- Prove2me | Theorems.Thm_GaugeFunctor_barrett_reconstruction
-- name    : GaugeFunctor.barrett_reconstruction
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T09:55:53.296142+00:00
-- url     : https://prove2.me/theorems/14d726a2-6262-4093-b852-79cb62bdef44
-- title:
--   Barrett reconstruction: every holonomy map comes from a connection
-- statement:
--   Setting: $X$ is a finite directed graph with vertex set $V=\{0,\dots,n_V-1\}$, edge set $E$ and maps $\mathrm{src},\mathrm{tgt}:E\to V$; a walk may use edges in either direction, and $X$ is *connected from* $x$ if every vertex is reached by a walk from $x$. $G$ is any group. A connection is $A:E\to G$; its holonomy $\mathrm{hol}_A(w)$ along a walk $w$ is the ordered product of $A(e)$ on forward steps and $A(e)^{-1}$ on backward steps. A gauge transformation $g:V\to G$ acts by $(g\cdot A)(e)=g(\mathrm{src}\,e)\,A(e)\,g(\mathrm{tgt}\,e)^{-1}$. $\mathsf{Pot}_G(X)$ is the category whose objects are connections and whose arrows $A\to B$ are gauge transformations $g$ with $g\cdot A=B$. $\mathsf{Hol}_x$ is the category of holonomy maps at $x$ (assignments $H$ of group elements to walks, multiplicative on loops at $x$ and unchanged by inserting a backtrack into a loop at $x$), with arrows $h:H\to H'$ the elements $h\in G$ such that $H'(\gamma)=h\,H(\gamma)\,h^{-1}$ for every loop $\gamma$ at $x$. The holonomy functor $\mathrm{hol}_x:\mathsf{Pot}_G(X)\to\mathsf{Hol}_x$ sends $A\mapsto\mathrm{hol}_A$ and $g\mapsto g(x)$.
--
--   **Statement.** If $X$ is connected from $x$, then for every holonomy map $H$ at $x$ there is a connection $A$ with $$\mathrm{hol}_A(\gamma)=H(\gamma)\quad\text{for every loop }\gamma\text{ at }x.$$
-- source:
--   S. Rosenstock, J. O. Weatherall, A categorical equivalence between generalized holonomy maps on a connected manifold and principal connections on bundles over that manifold, J. Math. Phys. 57 (2016) 102902, https://arxiv.org/abs/1504.02401, p. 3 (Barrett reconstruction theorem). Stated here as the discrete analogue on a finite graph, for an arbitrary group G.

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

/-- Discrete Barrett reconstruction: on a graph connected from `x`, every holonomy map at `x`
is the holonomy of some connection, on all loops at `x`. -/
theorem barrett_reconstruction (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) (H : HolMap X G x) :
    ∃ A : Fin X.nE → G, ∀ γ, X.IsPath x γ x → hol X G A γ = H.toFun γ := by sorry

end GaugeFunctor
