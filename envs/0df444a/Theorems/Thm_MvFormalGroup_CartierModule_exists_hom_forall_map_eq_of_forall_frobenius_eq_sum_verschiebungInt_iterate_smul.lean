-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul
-- name    : MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/96e6c03b-02d7-5c00-ae92-d679197e8610
-- title:
--   Cartier presentation: a homomorphism matching prescribed curves
-- statement:
--   Fix a prime $p$ and a commutative ring $R$ carrying a $\mathbb{Z}_p$-algebra structure, and let $\Phi$ and $\Psi$ be commutative formal group laws over $R$ of dimensions $d$ and $d'$ — that is, tuples of power series in two blocks of variables with vanishing constant terms, linear coefficients $\delta_{ij}$ in each block, associative, and symmetric under interchanging the two blocks. Elements of the Cartier module $\mathrm{CartierModule}\ p\ \Phi$ are $d$-tuples of power series in variables indexed by $\mathbb{N}$, with vanishing constant terms, intertwining substitution of the Witt addition law with addition along $\Phi$; `tangent` reads off the coefficient of the first variable in each component, `frobenius` and `verschiebungInt` are the additive endomorphisms given by substituting the Witt endomorphism families `verFam` and `frobPolyFam`. Given $f : \mathrm{Fin}\ d \to \mathrm{CartierModule}\ p\ \Phi$ whose tangent vectors are the standard basis, $\mathrm{tangent}(f_i)_j = \delta_{ij}$, coefficients $w_{m,i,l} \in W(R)$, remainders $h_{N,i}$ in the Cartier module of $\Phi$ and $h'_{N,i}$ in that of $\Psi$, and $g : \mathrm{Fin}\ d \to \mathrm{CartierModule}\ p\ \Psi$, assume that for every $N$ and every $i$ both $$F f_i = \sum_{m<N} V^m\Bigl(\sum_l w_{m,i,l}\cdot f_l\Bigr) + V^N h_{N,i}, \qquad F g_i = \sum_{m<N} V^m\Bigl(\sum_l w_{m,i,l}\cdot g_l\Bigr) + V^N h'_{N,i}$$ hold, with the same $w$ on both sides. Then there exists a homomorphism $\varphi : \Phi \to \Psi$ of formal group laws, i.e. a $d'$-tuple of power series in $d$ variables with zero constant terms satisfying the usual substitution identity, whose induced map on Cartier modules sends $f_l$ to $g_l$ for every $l$. No uniqueness of $\varphi$ is asserted.
--
--   This is Cartier's presentation theorem in the form used for formal groups over $\mathbb{Z}_p$-algebras: a commutative formal group law with a chosen basis of curves is determined by its structure equations, so that matching expansions of the Frobenius with coefficients in $W(R)$ produce a homomorphism carrying one family of curves to the other. It is used in the construction of formal $\mathcal{O}_D$-modules with prescribed homogeneous bases and structure constants, and in deducing the variant with Teichmüller coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul.lean

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

theorem MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra (PadicInt p) R] {d d' : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] (Ψ : MvFormalGroup d' R) [Ψ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : ∀ i j, MvFormalGroup.CartierModule.tangent (f i) j = if i = j then 1 else 0)
    (w : ℕ → Fin d → Fin d → WittVector p R)
    (h : ℕ → Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, w m i l • f l)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    (g : Fin d → MvFormalGroup.CartierModule p Ψ)
    (h' : ℕ → Fin d → MvFormalGroup.CartierModule p Ψ)
    (hexp' : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (g i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Ψ)))^[m]
          (∑ l : Fin d, w m i l • g l)) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Ψ)))^[N] (h' N i)) :
    ∃ φ : Φ.Hom Ψ, ∀ l, MvFormalGroup.CartierModule.map φ (f l) = g l := by sorry
