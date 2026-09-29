-- Prove2me | Theorems.Thm_NumberField_sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt
-- name    : NumberField.sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/ac635283-f68d-5c37-9ea8-6c5a985e9ab4
-- title:
--   Sign of Frobenius on G/H is (-1)^{[K:E]+rᵥ}
-- statement:
--   Let $E$ and $L$ be number fields with $L$ an $E$-algebra and $L/E$ Galois, and let $K$ be a number field that is an $E$-algebra and over which $L$ is an algebra, the two structures being compatible as a scalar tower over $E$. Let $v$ be a height-one prime of $\mathcal{O}_E$ whose ramification index in $\mathcal{O}_L$ equals $1$, let $Q$ be a height-one prime of $\mathcal{O}_L$ lying under which in $\mathcal{O}_E$ one finds $v$ (that is, $Q \cap \mathcal{O}_E = v$), and let $\sigma \in \mathrm{Gal}(L/E)$ be an arithmetic Frobenius at $Q$ over $\mathcal{O}_E$ in the sense of `IsArithFrobAt`. Consider the coset space of $\mathrm{Gal}(L/E)$ by the subgroup fixing the image of $K$ in $L$ (the field range of the $E$-algebra map $K \to L$ given by the scalar tower), on which $\sigma$ acts by left translation, and let `Equiv.Perm.sign` of the resulting permutation be viewed in $\mathbb{Z}$. The assertion is that this sign equals $(-1)^{d + r}$, where $d$ is the $E$-dimension of $K$ and $r$ is the cardinality of the fibre of $v$, namely the set of height-one primes $\mathfrak{P}$ of $\mathcal{O}_K$ with $\mathfrak{P} \cap \mathcal{O}_E = v$.
--
--   This is the Stickelberger-type sign computation underlying Hilbert ramification theory: the cycles of a Frobenius element acting on $\mathrm{Gal}(L/E)/\mathrm{Gal}(L/K)$ have lengths the residue degrees of the primes of $K$ above $v$, whose sum is $[K:E]$, so the sign is $(-1)^{[K:E]-r_v}$. It is used in the construction of admissible quadratic twists, where the sign character attached to a discriminant is evaluated at uniformiser idèles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt.lean

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

open scoped Classical in

theorem NumberField.sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt
    (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsGalois E L]
    (K : Type) [Field K] [NumberField K] [Algebra E K] [Algebra K L] [IsScalarTower E K L]
    (v : HeightOneSpectrum (𝓞 E)) (hv : Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1)
    (Q : HeightOneSpectrum (𝓞 L)) (hQ : Q.under (𝓞 E) = v)
    (σ : L ≃ₐ[E] L) (hσ : IsArithFrobAt (𝓞 E) σ Q.asIdeal) :
    ((Equiv.Perm.sign (MulAction.toPerm σ :
        Equiv.Perm ((L ≃ₐ[E] L) ⧸ (IsScalarTower.toAlgHom E K L).fieldRange.fixingSubgroup)) : ℤˣ) : ℤ) =
      (-1) ^ (Module.finrank E K + Nat.card (primeFibre E K v)) := by sorry
