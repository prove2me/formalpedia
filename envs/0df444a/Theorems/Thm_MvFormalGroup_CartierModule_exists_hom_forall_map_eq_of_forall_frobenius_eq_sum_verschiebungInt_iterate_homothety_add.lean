-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add
-- name    : MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/bcd333c8-2487-544a-bba7-dd2fd0eb072d
-- title:
--   Homomorphism of formal groups from matching V-adic expansions
-- statement:
--   Let $p$ be a prime and let $R$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure. Let $\Phi$ be a $d$-dimensional and $\Psi$ a $d'$-dimensional formal group law over $R$ (each given by power series in two blocks of variables with vanishing constant terms, identity linear parts and the associativity identity), both assumed commutative. Elements of [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162) are curves on $\Phi$, i.e. $d$-tuples of power series in variables indexed by $\mathbb{N}$ with vanishing constant terms that transform the Witt addition law into the group law of $\Phi$; they form an additive group, and `frobenius`, `verschiebungInt` and `homothety a` are the additive endomorphisms obtained by precomposing with the Witt endomorphisms given by `verFam`, `frobPolyFam` and `teichFam a` respectively, while `tangent` reads off the coefficient of the zeroth variable. Assume given curves $f_i$ on $\Phi$ ($i \in \mathrm{Fin}\ d$) whose tangent vectors are the standard basis, $\mathrm{tangent}(f_i)_j = \delta_{ij}$, scalars $c_{m,i,l} \in R$, and curves $h_{N,i}$ on $\Phi$ such that for all $N$ and $i$
--   $$F f_i = \sum_{m<N} V^m\Bigl(\sum_l \langle c_{m,i,l}\rangle f_l\Bigr) + V^N h_{N,i},$$
--   with $F$ = `frobenius`, $V$ = `verschiebungInt` and $\langle a \rangle$ = `homothety a`; assume further given curves $g_i$ on $\Psi$ and remainders $h'_{N,i}$ on $\Psi$ satisfying the same expansions with the same scalars $c_{m,i,l}$. Then there exists a homomorphism of formal group laws $\varphi : \Phi \to \Psi$ (a $d'$-tuple of power series in $d$ variables with vanishing constant terms compatible with the two group laws) such that pushing each $f_l$ forward along $\varphi$, i.e. substituting $f_l$ into $\varphi$, yields $g_l$ for every $l$.
--
--   This is the existence half of Cartier's presentation theorem at the level of formal group laws over an arbitrary $\mathbb{Z}_p$-algebra: a tuple of curves with standard tangent vectors and a prescribed $V$-adic expansion determines a homomorphism of laws realising any other tuple with the same expansion. It is used for the uniqueness-and-existence statement [`MvFormalGroup.CartierModule.existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion`](thm.html#MvFormalGroup.CartierModule.existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion), for [`MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_algebra_padicInt`](thm.html#MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_algebra_padicInt), and in the construction of $\mathbb{Z}_p^2$-actions from graded Frobenius expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add.lean

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

theorem MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_homothety_add
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra (PadicInt p) R] {d d' : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] (Ψ : MvFormalGroup d' R) [Ψ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : ∀ i j, MvFormalGroup.CartierModule.tangent (f i) j = if i = j then 1 else 0)
    (c : ℕ → Fin d → Fin d → R)
    (h : ℕ → Fin d → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i))
    (g : Fin d → MvFormalGroup.CartierModule p Ψ)
    (h' : ℕ → Fin d → MvFormalGroup.CartierModule p Ψ)
    (hexp' : ∀ (N : ℕ) (i : Fin d), MvFormalGroup.CartierModule.frobenius (g i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Ψ)))^[m]
          (∑ l : Fin d, MvFormalGroup.CartierModule.homothety (c m i l) (g l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Ψ)))^[N] (h' N i)) :
    ∃ φ : Φ.Hom Ψ, ∀ l, MvFormalGroup.CartierModule.map φ (f l) = g l := by sorry
