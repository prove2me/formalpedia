-- Prove2me | Theorems.Thm_HofmannStreicher1994_uip_formulations_iff
-- name    : HofmannStreicher1994.uip_formulations_iff
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-29T06:17:28.018992+00:00
-- url     : https://prove2.me/theorems/8d339d3d-0efa-4142-b00e-79e6e354eeed
-- title:
--   Section 1: Equivalence of the two UIP formulations
-- statement:
--   For every expression $A$ that is a well-formed type in the empty context, the following are equivalent in the specified object theory:
--
--   1. There is a derivable term of $\mathrm{Id}_{\mathrm{Id}_A(x,x)}(p,\mathrm{refl}_A(x))$ in context $x:A,p,q:\mathrm{Id}_A(x,x)$.
--   2. There is a derivable term of $\mathrm{Id}_{\mathrm{Id}_A(x,y)}(p,q)$ in context $x,y:A,p,q:\mathrm{Id}_A(x,y)$.
--
--   The source attributes this equivalence to the identity eliminator $J$. The unused $q$ in the first context is preserved. The theorem assumes only closed formation of $A$.
-- source:
--   Hofmann and Streicher, A Groupoid Model Refutes Uniqueness of Identity Proofs, author manuscript dated 21 March 1994, https://www.dcs.ed.ac.uk/home/mxh/SH.dvi.gz; LICS 1994, https://doi.org/10.1109/LICS.1994.316071. Section 1, manuscript p. 2, paragraph following Theorem 1.

import Definitions.Def_HofmannStreicher1994_Syntax

namespace HofmannStreicher1994

theorem uip_formulations_iff (A : Expr) (hA : TypeWf [] A) :
    (∃ t, TermWf (diagonalContext A) t (diagonalConclusion A)) ↔
      (∃ t, TermWf (uipContext A) t (uipConclusion A)) := by sorry

end HofmannStreicher1994
