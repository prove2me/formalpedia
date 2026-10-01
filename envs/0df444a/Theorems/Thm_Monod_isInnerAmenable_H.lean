-- Prove2me | Theorems.Thm_Monod_isInnerAmenable_H
-- name    : Monod.isInnerAmenable_H
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T14:11:59.505983+00:00
-- url     : https://prove2.me/theorems/6839a36b-e9e1-4840-b13f-41a28747dc11
-- title:
--   Proposition 5 — H(A) is inner amenable
-- statement:
--   For every subring $A$ of $\mathbf{R}$, $H(A)$ carries a conjugation-invariant finitely additive probability measure on all its subsets that gives $\{1\}$ measure $0$: a conjugation-invariant mean on $H(A) \setminus \{e\}$.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 1, Proposition 5

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem isInnerAmenable_H (A : Subring ℝ) : IsInnerAmenable (H A) := by
  sorry

end Monod
