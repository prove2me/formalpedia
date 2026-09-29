-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_isUnit_det_tangent_and_frobenius_expansion_baseChange
-- name    : MvFormalGroup.CartierModule.isUnit_det_tangent_and_frobenius_expansion_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/99b3ef4b-ea5e-5b20-bb7d-d35ae76bacf4
-- title:
--   Base change of a V-basis with structure constants
-- statement:
--   Let $p$ be a prime, let $\varphi\colon R\to S$ be a homomorphism of commutative rings, and let $\Phi$ be a $d$-dimensional formal group law over $R$ (a $d$-tuple of power series in two families of $d$ variables with vanishing constant term, linear terms the two coordinates, and associative) which is commutative in the sense that interchanging the two families of variables fixes each component. Let $f\colon \mathrm{Fin}\,d\to \mathrm{CartierModule}\,p\,\Phi$, whose members are $d$-tuples of power series in variables indexed by $\mathbb N$ with zero constant term, compatible with the Witt addition law and the group law $\Phi$. Assume (i) the $d\times d$ matrix over $R$ with entries the tangent coordinates $\mathrm{tangent}(f_i)_k$, i.e. the coefficients of the first variable in the components of $f_i$, has unit determinant; and (ii) there are constants $c_{m,i,j}\in R$ ($m\in\mathbb N$) such that for all $i$ and all $N$ some $h$ satisfies $\mathrm{frobenius}(f_i)=\sum_{m<N}V^m\bigl(\sum_j \mathrm{homothety}(c_{m,i,j})(f_j)\bigr)+V^N h$, where $V=\mathrm{verschiebungInt}$ and $\mathrm{frobenius}$, $V$, $\mathrm{homothety}(a)$ are the operators given by substitution of the Verschiebung, Frobenius-polynomial and Teichmüller families. Then, with $\Phi.\mathrm{map}\,\varphi$ commutative via [`MvFormalGroup.isComm_map`](def/MvFormalGroup_CartierModuleBaseChange.html#L22), the tangent matrix of the base-changed family $\mathrm{baseChange}\,\varphi\,(f_i)$ again has unit determinant, and for all $i,N$ there is $h$ in $\mathrm{CartierModule}\,p\,(\Phi.\mathrm{map}\,\varphi)$ with $\mathrm{frobenius}(\mathrm{baseChange}\,\varphi\,(f_i))=\sum_{m<N}V^m\bigl(\sum_j \mathrm{homothety}(\varphi(c_{m,i,j}))(\mathrm{baseChange}\,\varphi\,(f_j))\bigr)+V^N h$.
--
--   This is the base-change step for $V$-bases of the Cartier module $\operatorname{Hom}(\widehat W,\Phi)$: a $V$-basis with structure constants $c_{m,i,j}$ pushes forward along $\varphi\colon R\to S$ to a $V$-basis of the Cartier module of $\Phi\otimes_R S$ with structure constants $\varphi(c_{m,i,j})$. It is used by [`MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X`](thm.html#MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X) and [`MvFormalGroup.exists_cartierModule_vBasis_of_frobenius_expansion`](thm.html#MvFormalGroup.exists_cartierModule_vBasis_of_frobenius_expansion) to transport the universal construction of such bases to an arbitrary base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_isUnit_det_tangent_and_frobenius_expansion_baseChange.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem MvFormalGroup.CartierModule.isUnit_det_tangent_and_frobenius_expansion_baseChange
    (p : ℕ) [Fact p.Prime] {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)
    {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : IsUnit (Matrix.of fun i k => MvFormalGroup.CartierModule.tangent (f i) k).det)
    (c : ℕ → Fin d → Fin d → R)
    (hc : ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ,
      MvFormalGroup.CartierModule.frobenius (f i) =
        (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
          (∑ j : Fin d, MvFormalGroup.CartierModule.homothety (c m i j) (f j))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] h) :
    letI : (Φ.map φ).IsComm := MvFormalGroup.isComm_map Φ φ
    IsUnit (Matrix.of fun i k =>
        MvFormalGroup.CartierModule.tangent (MvFormalGroup.CartierModule.baseChange φ (f i)) k).det ∧
      ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p (Φ.map φ),
        MvFormalGroup.CartierModule.frobenius (MvFormalGroup.CartierModule.baseChange φ (f i)) =
          (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ.map φ)))^[(m : ℕ)]
            (∑ j : Fin d, MvFormalGroup.CartierModule.homothety (φ (c m i j))
              (MvFormalGroup.CartierModule.baseChange φ (f j)))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ.map φ)))^[N] h := by sorry
