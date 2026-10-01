-- Prove2me | Theorems.Thm_Monod_not_isAmenable_H
-- name    : Monod.not_isAmenable_H
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T14:13:55.282689+00:00
-- url     : https://prove2.me/theorems/ce110990-7cee-4a8c-908c-b639d520f8ca
-- title:
--   Theorem 1 — H(A) is non-amenable if A ≠ ℤ
-- statement:
--   Monod states (p. 1): “The main result of this article is the following, which relies on a new method for proving non-amenability.” “Theorem 1. The group $H(A)$ is non-amenable if $A \neq \mathbf{Z}$.”
--
--   In Lean: for every subring $A$ of $\mathbf{R}$ other than $\mathbf{Z}$, the group $H(A)$ of piecewise $\mathrm{PSL}_2(A)$ homeomorphisms of $\mathbf{P}^1$ fixing $\infty$ is not amenable: it carries no left-invariant finitely additive probability measure on all its subsets.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 1, Theorem 1

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem not_isAmenable_H {A : Subring ℝ} (hA : A ≠ ⊥) : ¬ Garrido.IsAmenable (H A) := by
  sorry

end Monod
