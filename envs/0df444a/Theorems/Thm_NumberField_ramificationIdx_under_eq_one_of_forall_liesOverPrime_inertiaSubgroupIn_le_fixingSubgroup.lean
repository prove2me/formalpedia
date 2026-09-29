-- Prove2me | Theorems.Thm_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
-- name    : NumberField.ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/35abcc7e-5465-5691-9e1b-bc44343f9baa
-- title:
--   Trivial inertia above ℓ forces e(Q∣ Q∩𝒪_K)=1
-- statement:
--   Let $K$ be a number field, and let $L$ be an intermediate field of $\operatorname{AlgebraicClosure}(\mathbb{Q})/\mathbb{Q}$ that is finite-dimensional and Galois over $\mathbb{Q}$; let $\varphi_L : K \to L$ be a $\mathbb{Q}$-algebra homomorphism, by which $L$ is regarded as a $K$-algebra in the conclusion, and let $\ell$ be a prime number. The hypothesis is that for every valuation subring $P$ of $\operatorname{AlgebraicClosure}(\mathbb{Q})$ such that $\ell$, viewed in $\operatorname{AlgebraicClosure}(\mathbb{Q})$, lies in the set of nonunits of $P$, the subgroup of $\operatorname{Gal}(\operatorname{AlgebraicClosure}(\mathbb{Q})/\mathbb{Q})$ obtained as the image of the inertia subgroup of $P$ under the inclusion of the decomposition subgroup of $P$ is contained in the fixing subgroup of $L$, i.e. consists of automorphisms fixing $L$ pointwise. The conclusion is that for every maximal ideal $Q$ of the ring of integers $\mathcal{O}_L$ containing the image of $\ell$, the ramification index `Ideal.ramificationIdx'` of $Q$ over its contraction $Q \cap \mathcal{O}_K$ (the ideal `Q.under (𝓞 K)`, formed using the $K$-algebra structure coming from $\varphi_L$) equals $1$.
--
--   This is the single-prime form of Hilbert's criterion that triviality of inertia implies unramifiedness: the inertia condition is imposed only at the valuation subrings of $\overline{\mathbb{Q}}$ above the one prime $\ell$, and the conclusion concerns only the primes of $\mathcal{O}_L$ above $\ell$. It is used in the level-arithmetic part of the development, where unramifiedness of auxiliary number fields at specified primes is needed to control $S$-units, $S$-class groups and Selmer-type cohomology groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField
open scoped NumberField

set_option autoImplicit false

theorem NumberField.ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
    (K : Type) [Field K] [NumberField K]
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (φL : K →ₐ[ℚ] L)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hHin : ∀ P : ValuationSubring (AlgebraicClosure ℚ),
      P.LiesOverPrime ℓ → P.inertiaSubgroupIn ℚ ≤ L.fixingSubgroup) :
    letI : Algebra K L := φL.toRingHom.toAlgebra
    ∀ Q : Ideal (𝓞 L), Q.IsMaximal → (ℓ : 𝓞 L) ∈ Q →
      Ideal.ramificationIdx' (Q.under (𝓞 K)) Q = 1 := by sorry
