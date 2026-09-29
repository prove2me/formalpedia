-- Prove2me | Theorems.Thm_MvFormalGroup_exists_hom_comp_eq_id_tangent_map_eq_of_isUnit_det
-- name    : MvFormalGroup.exists_hom_comp_eq_id_tangent_map_eq_of_isUnit_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/6c8d2164-b1fd-5fc7-859f-1b076be0b2cf
-- title:
--   Normalising tangents of a V-basis by coordinate change
-- statement:
--   Let $R$ be a commutative ring, $p$ a prime, $d$ a natural number and $\Phi$ a $d$-dimensional formal group law over $R$, i.e. a $d$-tuple of power series $\Phi_i$ in the variables $X_{\mathrm{inl}\,j},X_{\mathrm{inr}\,j}$ ($j\in\mathrm{Fin}\,d$) with zero constant term, linear part $X_{\mathrm{inl}\,i}+X_{\mathrm{inr}\,i}$ and the associativity identity, assumed commutative in the sense that interchanging the two blocks of variables fixes each $\Phi_i$. Let $f_1,\dots,f_d$ be elements of the Cartier module $\mathrm{CartierModule}\,p\,\Phi$, each being a $d$-tuple of power series in variables indexed by $\mathbb{N}$, with zero constant terms, such that substituting the Witt addition laws $\mathrm{addFam}\,p\,R$ (the images in $R$ of `WittVector.wittAdd`) into the tuple agrees with substituting the two variable blocks into $\Phi$; and let $\mathrm{tangent}(f)_j$ denote the coefficient of the degree-one monomial in the variable indexed by $0$ in the $j$-th component. Assume the matrix $(\mathrm{tangent}(f_i)_j)_{i,j}$ has unit determinant. Then there exist a $d$-dimensional commutative formal group law $\Phi'$ over $R$ and homomorphisms $\varphi\colon\Phi\to\Phi'$, $\psi\colon\Phi'\to\Phi$ with $\varphi\circ\psi=\mathrm{id}_{\Phi'}$ and $\psi\circ\varphi=\mathrm{id}_{\Phi}$, such that the pushed-forward elements $\varphi_*f_i$ satisfy $\mathrm{tangent}(\varphi_*f_i)_j=\delta_{ij}$ for all $i,j$.
--
--   This is the classical linear normalisation of a $V$-basis: a law admitting $d$ homomorphisms from the formal Witt group whose tangent vectors form a basis of $R^d$ is isomorphic, by a linear change of coordinates of the law, to one for which those tangent vectors are the standard basis vectors. It is the normalisation step preceding Cartier-theoretic presentations, and is used here in the construction of homogeneous $V$-bases for formal $\mathcal{O}_D$-modules and in the uniqueness statement for additive maps determined by Frobenius expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_exists_hom_comp_eq_id_tangent_map_eq_of_isUnit_det.lean

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

theorem MvFormalGroup.exists_hom_comp_eq_id_tangent_map_eq_of_isUnit_det
    {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : IsUnit (Matrix.of fun i j => MvFormalGroup.CartierModule.tangent (f i) j).det) :
    ∃ (Φ' : MvFormalGroup d R) (_ : Φ'.IsComm) (φ : Φ.Hom Φ') (ψ : Φ'.Hom Φ),
      φ.comp ψ = MvFormalGroup.Hom.id Φ' ∧ ψ.comp φ = MvFormalGroup.Hom.id Φ ∧
      ∀ i j, MvFormalGroup.CartierModule.tangent (MvFormalGroup.CartierModule.map φ (f i)) j =
        if i = j then 1 else 0 := by sorry
