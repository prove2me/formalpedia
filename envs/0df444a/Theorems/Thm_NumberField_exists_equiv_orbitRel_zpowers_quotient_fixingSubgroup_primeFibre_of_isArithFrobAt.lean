-- Prove2me | Theorems.Thm_NumberField_exists_equiv_orbitRel_zpowers_quotient_fixingSubgroup_primeFibre_of_isArithFrobAt
-- name    : NumberField.exists_equiv_orbitRel_zpowers_quotient_fixingSubgroup_primeFibre_of_isArithFrobAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/bd77cee1-6265-5747-8519-4fe07e19ec2e
-- title:
--   Frobenius orbits on cosets match primes above v
-- statement:
--   Let $E \subseteq L$ be number fields with $L/E$ Galois, let $K$ be an intermediate field of $L/E$, and write $G = \mathrm{Gal}(L/E)$ and $H =$ `K.fixingSubgroup`. Let $v$ be a height-one prime of $\mathcal{O}_E$ whose common ramification index in $\mathcal{O}_L$, `Ideal.ramificationIdxIn v.asIdeal (𝓞 L)`, equals $1$, let $Q$ be a height-one prime of $\mathcal{O}_L$ lying under which $v$ sits, i.e. `Q.under (𝓞 E) = v`, and let $\sigma \in G$ satisfy `IsArithFrobAt (𝓞 E) σ Q.asIdeal`, so that $\sigma$ is an arithmetic Frobenius at $Q$ over $\mathcal{O}_E$. Let the cyclic subgroup $\langle\sigma\rangle$ act by left translation on the coset space $G/H$. The assertion is that there exists a bijection $e$ from the set of $\langle\sigma\rangle$-orbits on $G/H$ to `primeFibre E K v`, the set of height-one primes $\mathfrak{P}$ of $\mathcal{O}_K$ with $\mathfrak{P}$`.under (𝓞 E) = v`, such that for every coset $x \in G/H$ the cardinality of the $\langle\sigma\rangle$-orbit of $x$ equals `v.asIdeal.inertiaDeg'` of the prime of $\mathcal{O}_K$ assigned by $e$ to the orbit class of $x$.
--
--   This is Dedekind's dictionary between the cycle type of a Frobenius element acting on the cosets of an intermediate field's fixing subgroup and the splitting type of the prime in that intermediate field, the orbit lengths being the residue degrees. It is used to compute the sign of the permutation induced by Frobenius on such a coset space, in [`NumberField.sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt`](thm.html#NumberField.sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_equiv_orbitRel_zpowers_quotient_fixingSubgroup_primeFibre_of_isArithFrobAt.lean

import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.GroupTheory.Perm.Sign
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg
open scoped Pointwise

theorem NumberField.exists_equiv_orbitRel_zpowers_quotient_fixingSubgroup_primeFibre_of_isArithFrobAt
    (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsGalois E L]
    (K : IntermediateField E L)
    (v : HeightOneSpectrum (𝓞 E)) (hv : Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1)
    (Q : HeightOneSpectrum (𝓞 L)) (hQ : Q.under (𝓞 E) = v)
    (σ : L ≃ₐ[E] L) (hσ : IsArithFrobAt (𝓞 E) σ Q.asIdeal) :
    ∃ e : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ((L ≃ₐ[E] L) ⧸ K.fixingSubgroup) ≃ primeFibre E K v,
      ∀ x : (L ≃ₐ[E] L) ⧸ K.fixingSubgroup,
        Nat.card (MulAction.orbit (Subgroup.zpowers σ) x) =
          v.asIdeal.inertiaDeg' ((e (Quotient.mk _ x) : HeightOneSpectrum (𝓞 K)).asIdeal) := by sorry
