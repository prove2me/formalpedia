-- Prove2me | Theorems.Thm_Monod_fixSubgroup_eq_bot_or_isCoamenable
-- name    : Monod.fixSubgroup_eq_bot_or_isCoamenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T14:06:39.978557+00:00
-- url     : https://prove2.me/theorems/b2ad217f-e191-401d-9f95-ba30219d74fb
-- title:
--   Proposition 7 — pointwise stabilizers in H(A) are co-amenable, or trivial for dense sets
-- statement:
--   Let $A$ be a subring of $\mathbf{R}$ and $E \subseteq \mathbf{P}^1$. If $E$ is dense, the subgroup of $H(A)$ fixing $E$ pointwise is trivial; if $E$ is not dense, that subgroup is co-amenable in $H(A)$.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 1, Proposition 7

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem fixSubgroup_eq_bot_or_isCoamenable (A : Subring ℝ) (E : Set (OnePoint ℝ)) :
    (Dense E → fixSubgroup (H A) E = ⊥) ∧ (¬ Dense E → IsCoamenable (fixSubgroup (H A) E)) := by
  sorry

end Monod
