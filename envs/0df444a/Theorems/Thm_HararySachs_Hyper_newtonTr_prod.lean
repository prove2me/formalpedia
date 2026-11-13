-- Prove2me | Theorems.Thm_HararySachs_Hyper_newtonTr_prod
-- name    : HararySachs.Hyper.newtonTr_prod
-- status  : Proved
-- author  : @milia
-- created : 2026-11-13T04:34:19.602858+00:00
-- url     : https://prove2.me/theorems/8229c692-ab68-4da5-adba-1dd96dae3df1
-- title:
--   Newton traces are additive over products
-- statement:
--   Let $R$ be a commutative ring and let $\Phi_l \in R[z]$, for $l$ in a finite set $s$, be polynomials with constant term $1$. Then for every $m$ the Newton traces satisfy
--   $$\tau_m\Bigl(\prod_{l\in s}\Phi_l\Bigr) = \sum_{l\in s}\tau_m(\Phi_l).$$
--   Over $\mathbb{Q}$ this is $\log\prod_l\Phi_l = \sum_l\log\Phi_l$. Over a general ring, $\tau_m$ is defined by Newton's recursion $m\,\Phi_m = -\sum_{j=1}^m\tau_j\,\Phi_{m-j}$, which is solvable because $\Phi_0 = 1$.
--
--   **Formalization Note** The Newton traces are `newtonTr`, with $\tau_0 = 0$.
-- source:
--   Additivity of the logarithm; mission strategy comments 8357894d-0c47-45af-94e5-d71263b245a7 and 5f345eb5-bd58-46fc-8bd2-52a8bf0241e1.

import Mathlib
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

/-- Newton traces are additive over products of polynomials with constant term `1`. -/
theorem newtonTr_prod {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (Φ : ι → Polynomial R) (h : ∀ l ∈ s, (Φ l).coeff 0 = 1) (m : ℕ) :
    newtonTr (∏ l ∈ s, Φ l) m = ∑ l ∈ s, newtonTr (Φ l) m := by
  sorry

end HararySachs.Hyper
