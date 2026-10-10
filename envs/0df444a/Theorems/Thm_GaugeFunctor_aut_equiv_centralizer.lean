-- Prove2me | Theorems.Thm_GaugeFunctor_aut_equiv_centralizer
-- name    : GaugeFunctor.aut_equiv_centralizer
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T09:57:08.547408+00:00
-- url     : https://prove2.me/theorems/457aed2a-71ab-4455-a46d-0288c82ecfa6
-- title:
--   Gauge stabilizer equals the centralizer of the holonomies
-- statement:
--   Setting: $X$ is a finite directed graph with vertex set $V=\{0,\dots,n_V-1\}$, edge set $E$ and maps $\mathrm{src},\mathrm{tgt}:E\to V$; a walk may use edges in either direction, and $X$ is *connected from* $x$ if every vertex is reached by a walk from $x$. $G$ is any group. A connection is $A:E\to G$; its holonomy $\mathrm{hol}_A(w)$ along a walk $w$ is the ordered product of $A(e)$ on forward steps and $A(e)^{-1}$ on backward steps. A gauge transformation $g:V\to G$ acts by $(g\cdot A)(e)=g(\mathrm{src}\,e)\,A(e)\,g(\mathrm{tgt}\,e)^{-1}$. $\mathsf{Pot}_G(X)$ is the category whose objects are connections and whose arrows $A\to B$ are gauge transformations $g$ with $g\cdot A=B$. $\mathsf{Hol}_x$ is the category of holonomy maps at $x$ (assignments $H$ of group elements to walks, multiplicative on loops at $x$ and unchanged by inserting a backtrack into a loop at $x$), with arrows $h:H\to H'$ the elements $h\in G$ such that $H'(\gamma)=h\,H(\gamma)\,h^{-1}$ for every loop $\gamma$ at $x$. The holonomy functor $\mathrm{hol}_x:\mathsf{Pot}_G(X)\to\mathsf{Hol}_x$ sends $A\mapsto\mathrm{hol}_A$ and $g\mapsto g(x)$.
--
--   **Statement.** If $X$ is connected from $x$ and $A$ is a connection, then evaluation at $x$, $g\mapsto g(x)$, is a bijection $$\{g:V\to G \mid g\cdot A=A\}\;\xrightarrow{\ \sim\ }\;\{h\in G \mid h\,\mathrm{hol}_A(\gamma)=\mathrm{hol}_A(\gamma)\,h \text{ for every loop } \gamma \text{ at } x\}.$$
-- source:
--   D. S. Freed, F. Quinn, Chern-Simons theory with finite gauge group, Commun. Math. Phys. 156 (1993) 435-472, https://arxiv.org/abs/hep-th/9111004, §3, eqs. (3.11)-(3.13) (automorphisms of a G-field form the centralizer). Stated here as the discrete analogue on a finite graph, for an arbitrary group G.

import Mathlib
import Definitions.Def_GaugeFunctor_defs

open CategoryTheory

namespace GaugeFunctor

/-- The gauge stabilizer of a connection on a graph connected from `x` is in bijection, via
evaluation at `x`, to the centralizer of its holonomy group at `x` (the non-abelian `H⁰`). -/
theorem aut_equiv_centralizer (X : Graph) (G : Type) [Group G] (x : Fin X.nV)
    (hX : X.Connected x) (A : Fin X.nE → G) :
    ∃ e : {g : Fin X.nV → G // gaugeAct X G g A = A} ≃
        {h : G // ∀ γ, X.IsPath x γ x → Commute h (hol X G A γ)},
      ∀ g, (e g).1 = g.1 x := by sorry

end GaugeFunctor
