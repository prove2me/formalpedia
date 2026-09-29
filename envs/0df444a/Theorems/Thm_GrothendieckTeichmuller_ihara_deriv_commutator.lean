-- Prove2me | Theorems.Thm_GrothendieckTeichmuller_ihara_deriv_commutator
-- name    : GrothendieckTeichmuller.ihara_deriv_commutator
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T21:30:44.751877+00:00
-- url     : https://prove2.me/theorems/8394ec79-da92-4c9c-93a1-e40e264163c7
-- title:
--   Lemma 7.2 — commutator of Ihara derivations
-- statement:
--   Let $\mathbb F(x,y)$ be the free Lie algebra over $\mathbb Q$ on two generators and, for $f \in \mathbb F(x,y)$, let $D_f$ be the Ihara derivation, i.e. the derivation determined by $D_f x = 0$ and $D_f y = [y,f]$.
--
--   For all $f, g \in \mathbb F(x,y)$,
--
--   $$[D_f, D_g] \;=\; D_{[f,g]} \;+\; D_{D_f g} \;-\; D_{D_g f},$$
--
--   an identity of derivations of $\mathbb F(x,y)$, the bracket on the left being the commutator of derivations.
--
--   Combined with the additivity of $f \mapsto D_f$, the identity says exactly that $[D_f,D_g] = D_{\{f,g\}}$ for the Ihara bracket $\{f,g\} = [f,g] + D_f g - D_g f$: the assignment $f \mapsto D_f$ intertwines the Ihara bracket with the commutator of derivations. It is the computational heart of the statement that the Ihara bracket is a Lie bracket.
-- source:
--   Thomas Willwacher, The Grothendieck-Teichmüller Group, ETH Zürich lecture notes (in progress), 27 February 2014, Section 7.3, p. 55 (Lemma 7.2, Corollary 7.1, Remarks 7.1 and 7.2); Remark 4.4, p. 47

import Definitions.Def_GT_grt1

namespace GrothendieckTeichmuller

theorem ihara_deriv_commutator (f g : Lxy) :
    ⁅iharaDeriv f, iharaDeriv g⁆ =
      iharaDeriv ⁅f, g⁆ + iharaDeriv (iharaDeriv f g) - iharaDeriv (iharaDeriv g f) := by sorry

end GrothendieckTeichmuller
