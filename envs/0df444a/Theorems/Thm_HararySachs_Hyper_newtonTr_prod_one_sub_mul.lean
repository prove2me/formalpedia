-- Prove2me | Theorems.Thm_HararySachs_Hyper_newtonTr_prod_one_sub_mul
-- name    : HararySachs.Hyper.newtonTr_prod_one_sub_mul
-- status  : Proved
-- author  : @milia
-- created : 2026-11-13T03:02:09.129938+00:00
-- url     : https://prove2.me/theorems/270dfc0c-0c20-426a-877d-90a37e62664c
-- title:
--   Newton traces of a product of linear factors are power sums
-- statement:
--   Let $R$ be a commutative ring, let $b_l \in R$ for $l$ in a finite set $L$, and let
--   $$\Phi(z) = \prod_{l \in L}\bigl(1 - b_l z\bigr).$$
--   Let $\tau_m$ be the Newton traces of $\Phi$, defined by $\tau_0 = 0$ and $\tau_m = -m\,\Phi_m - \sum_{j=1}^{m-1}\tau_j\,\Phi_{m-j}$. Then for every $m \ge 1$,
--   $$\tau_m = \sum_{l \in L} b_l^{\,m}.$$
--
--   These are Newton's identities in the form $\log\prod_l (1 - b_l z) = -\sum_{m\ge1} p_m z^m/m$, with $p_m$ the power sums. Applied to Poisson's product formula, they identify the row-graded logarithm of the resultant with sums of powers of point evaluations.
--
--   **Formalization Note** The identity holds over any commutative ring, since the recursion involves no division.
-- source:
--   Newton's identities for power sums and elementary symmetric polynomials; see e.g. Macdonald, Symmetric Functions and Hall Polynomials, 2nd ed., Ch. I, eq. (2.11').

import Mathlib
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

theorem newtonTr_prod_one_sub_mul {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (b : ι → R) (m : ℕ) (hm : 1 ≤ m) :
    newtonTr (∏ l ∈ s, (1 - Polynomial.C (b l) * Polynomial.X)) m = ∑ l ∈ s, b l ^ m := by
  sorry

end HararySachs.Hyper
