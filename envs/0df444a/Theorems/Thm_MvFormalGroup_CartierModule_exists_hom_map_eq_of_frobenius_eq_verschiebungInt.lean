-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_map_eq_of_frobenius_eq_verschiebungInt
-- name    : MvFormalGroup.CartierModule.exists_hom_map_eq_of_frobenius_eq_verschiebungInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/2375e3ed-e76e-5d83-b86b-9d4c90c39b75
-- title:
--   Cartier curves with Fγ=Vγ descend to a one-dimensional law
-- statement:
--   Let $p$ be a prime and let $R$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure. Let $d$ be a natural number and let $\Phi$ be a $d$-dimensional formal group law over $R$, that is, a $d$-tuple of power series in two families $(X_j)$, $(Y_j)$ of $d$ variables with zero constant term, linear coefficients given by the identity in each family, and satisfying the associativity identity; assume $\Phi$ is commutative, i.e. interchanging the two families of variables fixes each component. Let $\gamma$ be an element of the Cartier module [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162), i.e. a $d$-tuple of power series in variables indexed by $\mathbb{N}$, each with zero constant term, such that substituting the Witt addition polynomials for $p$ into each component agrees with substituting the two variable blocks into $\Phi$ (a $p$-typical curve on $\Phi$). Assume that `frobenius`, the operator given by precomposition with the Verschiebung substitution family, and `verschiebungInt`, precomposition with the Frobenius polynomial family, agree on $\gamma$. Then there exist a one-dimensional formal group law $H$ over $R$, a proof that $H$ is commutative, an element $\varepsilon$ of the Cartier module of $H$, and a homomorphism $\varphi : H \to \Phi$ of formal group laws (a power series with zero constant term satisfying the homomorphism identity) such that the tangent coefficient `tangent ε 0` — the coefficient of the first variable in $\varepsilon$ — is a unit of $R$ and the induced additive map `map φ` sends $\varepsilon$ to $\gamma$.
--
--   In Cartier theory this says that a $p$-typical curve on a commutative formal group law satisfying $F\gamma = V\gamma$ is the push-forward of a $V$-basis curve along a homomorphism from a one-dimensional formal group law, so that $\gamma$ parametrises a one-parameter formal subgroup of $\Phi$ (the structure constants $F\varepsilon = V\varepsilon$ being those of a height-two one-dimensional law). It is used in the analysis of formal modules in the Čerednik–Drinfeld part of the development, where the existence of such a one-dimensional factor yields membership of powers of the parameter in spans of the action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_exists_hom_map_eq_of_frobenius_eq_verschiebungInt.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.exists_hom_map_eq_of_frobenius_eq_verschiebungInt
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra (PadicInt p) R]
    {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (γ : MvFormalGroup.CartierModule p Φ)
    (hγ : MvFormalGroup.CartierModule.frobenius γ = MvFormalGroup.CartierModule.verschiebungInt γ) :
    ∃ (H : MvFormalGroup 1 R) (_ : H.IsComm) (ε : MvFormalGroup.CartierModule p H) (φ : H.Hom Φ),
      IsUnit (MvFormalGroup.CartierModule.tangent ε 0) ∧ MvFormalGroup.CartierModule.map φ ε = γ := by sorry
