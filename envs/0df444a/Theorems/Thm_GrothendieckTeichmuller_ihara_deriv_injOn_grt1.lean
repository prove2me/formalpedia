-- Prove2me | Theorems.Thm_GrothendieckTeichmuller_ihara_deriv_injOn_grt1
-- name    : GrothendieckTeichmuller.ihara_deriv_injOn_grt1
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T21:44:12.95593+00:00
-- url     : https://prove2.me/theorems/78752348-6d61-4b3a-a3ea-92a247ade4dc
-- title:
--   Injectivity of $f \mapsto D_f$ on $\mathfrak{grt}_1$
-- statement:
--   The map $f \mapsto D_f$ sending a Lie polynomial to its Ihara derivation ($D_f x = 0$, $D_f y = [y,f]$) is injective on $\mathfrak{grt}_1$: if $f, g \in \mathfrak{grt}_1$ and $D_f = D_g$, then $f = g$.
--
--   This is a supporting statement rather than a result of the source. It is needed because the Lie structure of $\mathfrak{grt}_1$ is carried, in this mission's formalization, by the embedding $f \mapsto D_f$ into the Lie algebra of derivations of $\mathbb F(x,y)$; injectivity on $\mathfrak{grt}_1$ is what makes statements formulated on the derivation side equivalent to statements about $\mathfrak{grt}_1$ itself.
--
--   The map is *not* injective on all of $\mathbb F(x,y)$: $D_y = 0$ while $y \ne 0$. Its kernel is the line spanned by $y$, which meets $\mathfrak{grt}_1$ only in $0$ because $y$ violates the antisymmetry equation.
-- source:
--   Thomas Willwacher, The Grothendieck-Teichmüller Group, ETH Zürich lecture notes (in progress), 27 February 2014, Section 7.3, p. 55 (Lemma 7.2, Corollary 7.1, Remarks 7.1 and 7.2); Remark 4.4, p. 47 (supporting statement for the encoding of the Lie structure of grt_1 via derivations; not itself numbered in the source)

import Definitions.Def_GT_grt1

namespace GrothendieckTeichmuller

theorem ihara_deriv_injOn_grt1 : Set.InjOn iharaDeriv (grt1 : Set Lxy) := by sorry

end GrothendieckTeichmuller
