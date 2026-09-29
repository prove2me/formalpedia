-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt
-- name    : MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/b291dc57-bb4f-5169-9d90-21b206060a2a
-- title:
--   Zero tangent vector implies being a Verschiebung value
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure, let $d$ be a natural number, and let $\Phi$ be a $d$-dimensional formal group law over $R$, that is, a $d$-tuple of power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with vanishing constant terms, linear coefficients given by the identity in each group of variables, and satisfying the associativity identity; assume moreover that $\Phi$ is commutative, i.e. interchanging the two groups of variables fixes each component. Let $f$ be an element of the Cartier module $\mathrm{CartierModule}\,p\,\Phi$: a $d$-tuple of power series $f_j$ in variables indexed by $\mathbb{N}$, each with zero constant term, such that substituting the $p$-typical Witt addition family `WittLaw.addFam p R` into $f_j$ agrees with substituting into the $j$-th component of $\Phi$ the pair of series obtained from $f$ by renaming the variables to the first, resp. second, block. Suppose the tangent vector of $f$ vanishes, i.e. the coefficient of the first variable $X_0$ in $f_j$ is $0$ for every $j$. Then there exists $g$ in the same Cartier module whose image under `verschiebungInt`, namely precomposition (substitution) with the integral Witt Frobenius family `WittLaw.frobPolyFam p R`, equals $f$.
--
--   This is the inclusion $\ker(\mathrm{tangent}) \subseteq V M$ for the module $M$ of $p$-typical curves on $\Phi$ over a $\mathbb{Z}_p$-algebra, the existence half of the identification $M/VM \cong \mathrm{Lie}\,\Phi$ in Cartier theory. It is used for the equivalence `tangent_eq_zero_iff_exists_verschiebungInt_eq`, for the unique $V$-adic expansion of a curve as a sum of Verschiebung iterates applied to homotheties, and for the construction of homomorphisms out of the Cartier module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra ℤ_[p] R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] (f : MvFormalGroup.CartierModule p Φ)
    (hf : MvFormalGroup.CartierModule.tangent f = 0) :
    ∃ g : MvFormalGroup.CartierModule p Φ, MvFormalGroup.CartierModule.verschiebungInt g = f := by sorry
