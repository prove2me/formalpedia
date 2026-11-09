-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_unit_clause_cost
-- name    : MajorityDepthThree.Exact.unit_clause_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:18.414331+00:00
-- url     : https://prove2.me/theorems/a37264a7-fc7e-4a51-bb11-1ba985034a1f
-- title:
--   Lemma 5.14 — exact unit-clause reduction
-- statement:
--   Let $F$ be a valid monotone CNF on the finite ground set $V$, let $n=|V|$, and suppose the positive unit clause $\{a\}$ belongs to $F$. Let $C_F$ be the covering minimum for $T(F)$ at the Section 5 parameters. Then
--
--   $$C_F=rC_{F[a=1]},\qquad \frac{C_F}{p^n}=\frac12\frac{C_{F[a=1]}}{p^{n-1}}.$$
--
--   The residual ground set removes $a$. Its family is exactly the satisfying sets containing $a$ with $a$ erased; the unit clause already forces containment. Both equalities are retained, including the normalization used by the simultaneous bounds.
--
--   Differences from the source:
--   - encoding: A finite ground set V and its subsets → Finite subsets V of a variable type, with finite families of subsets; reason: Every source instance has this representation; all assignments and ambient isolated variables are retained
--   - encoding: The residual formula F[a=1] on V minus a → Its computed satisfying-set family, obtained by filtering for a and erasing a; reason: The covering objective depends only on this family; the actual unit clause and validity imply a belongs to V, so n minus 1 is not truncated
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.15, Lemma 5.14

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false

namespace MajorityDepthThree.Exact

theorem unit_clause_cost {α : Type} [DecidableEq α] (V : Finset α)
    (F : CNF α) (hv : ValidCNF V F) (hm : Monotone F) (a : α)
    (ha : ({a}, ∅) ∈ F) :
    coverValue (transversals V F) r q = r * coverValue (setOne a (transversals V F)) r q ∧
    coverValue (transversals V F) r q / p ^ V.card =
      (1 / 2 : ℝ) * coverValue (setOne a (transversals V F)) r q / p ^ (V.card - 1) := by sorry

end MajorityDepthThree.Exact
