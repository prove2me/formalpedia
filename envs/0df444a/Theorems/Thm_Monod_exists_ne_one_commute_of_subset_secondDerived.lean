-- Prove2me | Theorems.Thm_Monod_exists_ne_one_commute_of_subset_secondDerived
-- name    : Monod.exists_ne_one_commute_of_subset_secondDerived
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T14:10:40.738152+00:00
-- url     : https://prove2.me/theorems/46c199fd-cf67-4ac6-a692-8e9c1eba0664
-- title:
--   Proposition 15 — a finite subset of H(A)″ commutes with a non-trivial element
-- statement:
--   Let $A$ be a subring of $\mathbf{R}$. For every finite set $S$ of elements of the second derived subgroup $H(A)''$ there is a non-identity $h \in H(A)$ commuting with every element of $S$.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 3, Proposition 15

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem exists_ne_one_commute_of_subset_secondDerived (A : Subring ℝ) (S : Finset (H A))
    (hS : ∀ s ∈ S, s ∈ derivedSeries (H A) 2) :
    ∃ h : H A, h ≠ 1 ∧ ∀ s ∈ S, Commute h s := by
  sorry

end Monod
