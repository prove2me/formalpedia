-- Prove2me | Theorems.Thm_HofmannStreicher1994_uip_underivable
-- name    : HofmannStreicher1994.uip_underivable
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-29T06:18:04.447251+00:00
-- url     : https://prove2.me/theorems/ff210ab2-6cf6-4fb0-bbf1-b53cc5bb281d
-- title:
--   Section 3: The explicit closed type refutes both UIP formulations
-- statement:
--   The expression $A_0=\Sigma X:U.\mathrm{El}(X)$ is a well-formed type in the empty context. No expression is derivably a term of $\mathrm{Id}_{\mathrm{Id}_{A_0}(x,x)}(p,\mathrm{refl}_{A_0}(x))$ in context $x:A_0,p,q:\mathrm{Id}_{A_0}(x,x)$. Nor is any expression derivably a term of $\mathrm{Id}_{\mathrm{Id}_{A_0}(x,y)}(p,q)$ in context $x,y:A_0,p,q:\mathrm{Id}_{A_0}(x,y)$.
--
--   All three clauses concern the specified annotated object theory, including the selected 1994 $U/\mathrm{El}$ interface. There is no model, interpretation, soundness, or non-UIP premise. The source's model, interpretation and soundness argument remain part of the work required to prove this unconditional statement.
-- source:
--   Hofmann and Streicher, A Groupoid Model Refutes Uniqueness of Identity Proofs, author manuscript dated 21 March 1994, https://www.dcs.ed.ac.uk/home/mxh/SH.dvi.gz; LICS 1994, https://doi.org/10.1109/LICS.1994.316071. Theorem 1 and following paragraph, manuscript p. 2; explicit witness in Section 3, p. 7.

import Definitions.Def_HofmannStreicher1994_Syntax

namespace HofmannStreicher1994

theorem uip_underivable :
    TypeWf [] counterexampleType ∧
      (¬ ∃ t, TermWf (diagonalContext counterexampleType) t
        (diagonalConclusion counterexampleType)) ∧
      (¬ ∃ t, TermWf (uipContext counterexampleType) t
        (uipConclusion counterexampleType)) := by sorry

end HofmannStreicher1994
