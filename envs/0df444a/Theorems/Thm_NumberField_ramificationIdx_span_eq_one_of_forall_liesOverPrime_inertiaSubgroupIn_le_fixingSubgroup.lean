-- Prove2me | Theorems.Thm_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
-- name    : NumberField.ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/f8ab765e-d233-5f86-b8c3-f2e2f5185b47
-- title:
--   Trivial inertia above ℓ implies e(Q∣ℓ)=1
-- statement:
--   Let $L$ be an intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is finite-dimensional and Galois over $\mathbb{Q}$, and let $\ell$ be a natural number that is prime. Assume that for every valuation subring $P$ of $\overline{\mathbb{Q}}$ which lies over $\ell$ in the sense of [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), that is, the image of $\ell$ in $\overline{\mathbb{Q}}$ is a non-unit of $P$, the subgroup `P.inertiaSubgroupIn ℚ` of $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ — the image of the inertia subgroup of $P$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup of $P$ into the full automorphism group — is contained in the fixing subgroup of $L$, i.e. every element of that inertia group fixes $L$ pointwise. The conclusion is that for every maximal ideal $Q$ of the ring of integers $\mathcal{O}_L$ containing the image of $\ell$, the ramification index `Ideal.ramificationIdx'` of $Q$ over the principal ideal $\ell\mathbb{Z} =$ `Ideal.span {(ℓ : ℤ)}` of $\mathbb{Z}$, taken for the canonical $\mathbb{Z}$-algebra structure on $\mathcal{O}_L$, equals $1$; in other words $\ell$ is unramified in $L$.
--
--   This is the absolute form, over the base field $\mathbb{Q}$, of the standard criterion of Hilbert ramification theory that a prime is unramified in a Galois extension exactly when the inertia groups above it are trivial. It feeds the arguments that $\mathcal{O}_L/\ell\mathcal{O}_L$ is reduced, and is used in the Herbrand-style level and cohomology computations that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField
open scoped NumberField

set_option autoImplicit false

theorem NumberField.ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hHin : ∀ P : ValuationSubring (AlgebraicClosure ℚ),
      P.LiesOverPrime ℓ → P.inertiaSubgroupIn ℚ ≤ L.fixingSubgroup) :
    ∀ Q : Ideal (𝓞 L), Q.IsMaximal → (ℓ : 𝓞 L) ∈ Q →
      Ideal.ramificationIdx' (Ideal.span {(ℓ : ℤ)}) Q = 1 := by sorry
