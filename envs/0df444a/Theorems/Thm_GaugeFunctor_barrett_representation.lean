-- Prove2me | Theorems.Thm_GaugeFunctor_barrett_representation
-- name    : GaugeFunctor.barrett_representation
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T09:56:37.967441+00:00
-- url     : https://prove2.me/theorems/b29e41ab-64d1-47aa-940e-e3ba3f56353d
-- title:
--   Barrett representation: equal holonomies iff gauge-equivalent fixing x
-- statement:
--   Setting: $X$ is a finite directed graph with vertex set $V=\{0,\dots,n_V-1\}$, edge set $E$ and maps $\mathrm{src},\mathrm{tgt}:E\to V$; a walk may use edges in either direction, and $X$ is *connected from* $x$ if every vertex is reached by a walk from $x$. $G$ is any group. A connection is $A:E\to G$; its holonomy $\mathrm{hol}_A(w)$ along a walk $w$ is the ordered product of $A(e)$ on forward steps and $A(e)^{-1}$ on backward steps. A gauge transformation $g:V\to G$ acts by $(g\cdot A)(e)=g(\mathrm{src}\,e)\,A(e)\,g(\mathrm{tgt}\,e)^{-1}$. $\mathsf{Pot}_G(X)$ is the category whose objects are connections and whose arrows $A\to B$ are gauge transformations $g$ with $g\cdot A=B$. $\mathsf{Hol}_x$ is the category of holonomy maps at $x$ (assignments $H$ of group elements to walks, multiplicative on loops at $x$ and unchanged by inserting a backtrack into a loop at $x$), with arrows $h:H\to H'$ the elements $h\in G$ such that $H'(\gamma)=h\,H(\gamma)\,h^{-1}$ for every loop $\gamma$ at $x$. The holonomy functor $\mathrm{hol}_x:\mathsf{Pot}_G(X)\to\mathsf{Hol}_x$ sends $A\mapsto\mathrm{hol}_A$ and $g\mapsto g(x)$.
--
--   **Statement.** If $X$ is connected from $x$, then for connections $A,B$: $\mathrm{hol}_A(\gamma)=\mathrm{hol}_B(\gamma)$ for every loop $\gamma$ at $x$ if and only if there is a **unique** gauge transformation $g$ with $g(x)=1$ and $g\cdot A=B$.
-- source:
--   S. Rosenstock, J. O. Weatherall, A categorical equivalence between generalized holonomy maps on a connected manifold and principal connections on bundles over that manifold, J. Math. Phys. 57 (2016) 102902, https://arxiv.org/abs/1504.02401, p. 3 (Barrett representation theorem). Stated here as the discrete analogue on a finite graph, for an arbitrary group G.

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

/-- Discrete Barrett representation: on a graph connected from `x`, two connections have the
same holonomy on every loop at `x` iff they differ by a gauge transformation trivial at `x`,
and that gauge transformation is then unique. -/
theorem barrett_representation (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) (A B : Fin X.nE → G) :
    (∀ γ, X.IsPath x γ x → hol X G A γ = hol X G B γ) ↔
      ∃! g : Fin X.nV → G, g x = 1 ∧ gaugeAct X G g A = B := by sorry

end GaugeFunctor
