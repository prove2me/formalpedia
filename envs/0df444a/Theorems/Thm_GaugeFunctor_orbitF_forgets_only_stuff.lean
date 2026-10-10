-- Prove2me | Theorems.Thm_GaugeFunctor_orbitF_forgets_only_stuff
-- name    : GaugeFunctor.orbitF_forgets_only_stuff
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T09:57:30.699674+00:00
-- url     : https://prove2.me/theorems/c24c30b1-1064-4136-9412-f1073394fe85
-- title:
--   The gauge-orbit functor forgets only stuff
-- statement:
--   Setting: $X$ is a finite directed graph with vertex set $V=\{0,\dots,n_V-1\}$, edge set $E$ and maps $\mathrm{src},\mathrm{tgt}:E\to V$; a walk may use edges in either direction, and $X$ is *connected from* $x$ if every vertex is reached by a walk from $x$. $G$ is any group. A connection is $A:E\to G$; its holonomy $\mathrm{hol}_A(w)$ along a walk $w$ is the ordered product of $A(e)$ on forward steps and $A(e)^{-1}$ on backward steps. A gauge transformation $g:V\to G$ acts by $(g\cdot A)(e)=g(\mathrm{src}\,e)\,A(e)\,g(\mathrm{tgt}\,e)^{-1}$. $\mathsf{Pot}_G(X)$ is the category whose objects are connections and whose arrows $A\to B$ are gauge transformations $g$ with $g\cdot A=B$. $\mathsf{Hol}_x$ is the category of holonomy maps at $x$ (assignments $H$ of group elements to walks, multiplicative on loops at $x$ and unchanged by inserting a backtrack into a loop at $x$), with arrows $h:H\to H'$ the elements $h\in G$ such that $H'(\gamma)=h\,H(\gamma)\,h^{-1}$ for every loop $\gamma$ at $x$. The holonomy functor $\mathrm{hol}_x:\mathsf{Pot}_G(X)\to\mathsf{Hol}_x$ sends $A\mapsto\mathrm{hol}_A$ and $g\mapsto g(x)$.
--
--   Let $\mathrm{orb}:\mathsf{Pot}_G(X)\to\mathcal{O}$ send each connection to its gauge orbit, where $\mathcal{O}$ is the discrete category (identity arrows only) on the set of gauge orbits.
--
--   **Statement.** For every finite graph $X$ (connected or not) and every group $G$, $\mathrm{orb}$ is full and essentially surjective, and it is faithful if and only if $X$ has no vertices or $G$ is trivial.
-- source:
--   J. Nguyen, N. J. Teh, L. Wells, Why surplus structure is not superfluous, Brit. J. Phil. Sci. 71 (2020), https://arxiv.org/abs/1712.01228, §3.2, Proposition 3.2.3 and fn. 26; J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (arXiv v2 includes the erratum, p. 15), erratum to Proposition 2. Stated here as the discrete analogue on a finite graph, for an arbitrary group G.

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

/-- The functor from connections-with-gauge-arrows to gauge orbits is full and essentially
surjective, and it is faithful exactly when the graph has no vertices or the gauge group is
trivial; otherwise it forgets only stuff (the global gauge transformations). -/
theorem orbitF_forgets_only_stuff (X : Graph) (G : Type) [Group G] :
    (orbitF X G).Full ∧ (orbitF X G).EssSurj ∧
      ((orbitF X G).Faithful ↔ (IsEmpty (Fin X.nV) ∨ Subsingleton G)) := by sorry

end GaugeFunctor
