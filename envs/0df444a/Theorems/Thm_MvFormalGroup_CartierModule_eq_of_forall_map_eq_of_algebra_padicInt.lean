-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_eq_of_forall_map_eq_of_algebra_padicInt
-- name    : MvFormalGroup.CartierModule.eq_of_forall_map_eq_of_algebra_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/e30eedb5-d2bb-5b12-ab5d-986b850fbf09
-- title:
--   Faithfulness of the Cartier module functor over ℤₚ-algebras
-- statement:
--   Fix a natural number $p$ carrying a `Fact` that it is prime, and a commutative ring $R$ (in universe $u$) equipped with an algebra structure over $\mathbb{Z}_p$ (`PadicInt p`). Let $d, d'$ be naturals and let $\Phi$, $\Phi'$ be formal group laws of dimensions $d$ and $d'$ over $R$, i.e. tuples of power series $\Phi_i \in R[[X_1,\dots,X_d,Y_1,\dots,Y_d]]$ (variables indexed by `Fin d ⊕ Fin d`) with vanishing constant coefficient, linear coefficients $\delta_{ij}$ in each of the two blocks, and the associativity identity between the two threefold substitutions; both are assumed commutative, in the sense that interchanging the two blocks of variables fixes each $\Phi_i$. Let $\varphi, \psi : \Phi \to \Phi'$ be homomorphisms of laws, each given by $d'$ power series in $d$ variables with zero constant coefficient satisfying the compatibility $\varphi \circ \Phi = \Phi' \circ (\varphi, \varphi)$ expressed by substitution. The hypothesis is that the induced additive maps on Cartier modules agree: for every $f$ in [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162) — that is, every tuple $(f_j)_{j<d}$ of power series in variables indexed by $\mathbb{N}$ with zero constant coefficient satisfying $\mathrm{subst}\,(\text{Witt addition family over } R)\,f_j = \mathrm{subst}$ of the two block-renamed copies of $f$ into $\Phi_j$ — one has `map φ f = map ψ f`, where the $i$-th component of `map φ f` is the substitution of $f$ into $\varphi_i$. The conclusion is $\varphi = \psi$.
--
--   This is the faithfulness of the Cartier module functor $\Phi \mapsto \operatorname{Hom}(\widehat W, \Phi)$ on commutative formal group laws over a $\mathbb{Z}_p$-algebra: a homomorphism of laws is determined by the additive map it induces on Witt curves. It is used as a uniqueness device in the construction of homomorphisms of formal $\mathcal{O}_D$-modules in the Cerednik–Drinfeld part of the development, where morphisms are produced at the level of Cartier modules and then transported back to the formal groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_eq_of_forall_map_eq_of_algebra_padicInt.lean

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

theorem MvFormalGroup.CartierModule.eq_of_forall_map_eq_of_algebra_padicInt
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R]
    [Algebra (PadicInt p) R]
    {d d' : ℕ} (Φ : MvFormalGroup d R) (Φ' : MvFormalGroup d' R) [Φ.IsComm] [Φ'.IsComm]
    (φ ψ : Φ.Hom Φ')
    (h : ∀ f : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.map φ f = MvFormalGroup.CartierModule.map ψ f) :
    φ = ψ := by sorry
