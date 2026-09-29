-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_subst_curve_eq_of_forall_map_eq_of_algebra_padicInt
-- name    : MvFormalGroup.CartierModule.subst_curve_eq_of_forall_map_eq_of_algebra_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/950cff51-51d4-5c0e-a9cc-5d3d8929f46b
-- title:
--   Homomorphisms agreeing on p-typical curves agree on all curves
-- statement:
--   Let $p$ be a prime and let $R$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure. Let $\Phi$ be a $d$-dimensional formal group law over $R$ and $\Phi'$ a $d'$-dimensional one, each given by a tuple of multivariate power series in two blocks of variables with vanishing constant terms, with the two blocks of linear coefficients equal to the identity matrix, and satisfying the associativity identity; assume both satisfy `IsComm`, i.e. interchanging the two blocks of variables fixes each component. Let $\varphi,\psi\colon\Phi\to\Phi'$ be homomorphisms, each a $d'$-tuple of power series in $d$ variables with zero constant term satisfying $\varphi\circ\Phi=\Phi'\circ(\varphi,\varphi)$ in the substitution sense. Assume that the induced additive maps on Cartier modules coincide: for every $f\in$ `CartierModule p Φ` — a $d$-tuple of power series in variables indexed by $\mathbb{N}$, with zero constant terms, turning the $p$-typical Witt addition family `WittLaw.addFam p R` into $\Phi$-addition — one has `map φ f = map ψ f`, where the components of `map φ f` are the substitutions of $f$ into the components of $\varphi$. Then for every curve $\gamma\colon \mathrm{Fin}\,d\to R[[t]]$ with all constant coefficients zero and every index $k\in\mathrm{Fin}\,d'$, substitution of $\gamma$ into the $k$-th component of $\varphi$ equals substitution of $\gamma$ into the $k$-th component of $\psi$.
--
--   This is Cartier's $p$-typification statement: over a $\mathbb{Z}_p$-algebra a homomorphism of commutative formal group laws is determined by its action on $p$-typical curves, because the big Witt formal group splits into copies of the $p$-typical one indexed by the integers prime to $p$. It is the computational core of [`MvFormalGroup.CartierModule.eq_of_forall_map_eq_of_algebra_padicInt`](thm.html#MvFormalGroup.CartierModule.eq_of_forall_map_eq_of_algebra_padicInt), which concludes that $\varphi=\psi$ as homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_subst_curve_eq_of_forall_map_eq_of_algebra_padicInt.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.subst_curve_eq_of_forall_map_eq_of_algebra_padicInt
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra (PadicInt p) R]
    {d d' : ℕ} (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R) [Φ.IsComm] [Φ'.IsComm]
    (φ ψ : Φ.Hom Φ')
    (h : ∀ f : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.map φ f = MvFormalGroup.CartierModule.map ψ f)
    (γ : Fin d → PowerSeries R) (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0) (k : Fin d') :
    MvPowerSeries.subst γ (φ.toPowerSeries k) = MvPowerSeries.subst γ (ψ.toPowerSeries k) := by sorry
