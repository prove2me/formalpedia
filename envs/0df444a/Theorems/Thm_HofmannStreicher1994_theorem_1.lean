-- Prove2me | Theorems.Thm_HofmannStreicher1994_theorem_1
-- name    : HofmannStreicher1994.theorem_1
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-29T06:18:15.314983+00:00
-- url     : https://prove2.me/theorems/1350ae48-4c23-422a-afda-87048668fece
-- title:
--   Theorem 1: A closed type with non-derivable uniqueness of identity proofs
-- statement:
--   There exists a type $A$ well formed in the empty context such that no expression is derivably a term of
--
--   $$\mathrm{Id}_{\mathrm{Id}_A(x,x)}(p,\mathrm{refl}_A(x))$$
--
--   in the context $x:A,p,q:\mathrm{Id}_A(x,x)$. This is the existential formulation printed as Theorem 1, retaining its unused $q$ binder, for the explicitly selected annotated object theory. It has no assumptions of a model, soundness, or semantic UIP failure. Section 3 supplies the witness $\Sigma X:U.\mathrm{El}(X)$.
-- source:
--   Hofmann and Streicher, A Groupoid Model Refutes Uniqueness of Identity Proofs, author manuscript dated 21 March 1994, https://www.dcs.ed.ac.uk/home/mxh/SH.dvi.gz; LICS 1994, https://doi.org/10.1109/LICS.1994.316071. Theorem 1, manuscript p. 2; proof and closed witness in Section 3, p. 7.

import Definitions.Def_HofmannStreicher1994_Syntax

namespace HofmannStreicher1994

theorem theorem_1 :
    ∃ A, TypeWf [] A ∧
      ¬ ∃ t, TermWf (diagonalContext A) t (diagonalConclusion A) := by sorry

end HofmannStreicher1994
