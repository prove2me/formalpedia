-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
-- name    : MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/4f451982-45f8-5bad-b1bb-61532c803e8f
-- title:
--   Unique finite V-expansion along a tangent basis
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure, let $d$ be a natural number and let $\Phi$ be a $d$-dimensional formal group law over $R$ — that is, $d$ power series in the variables indexed by $\mathrm{Fin}\,d \sqcup \mathrm{Fin}\,d$ with vanishing constant terms, identity linear parts in each block, and the associativity identity — which is moreover commutative in the sense of [`MvFormalGroup.IsComm`](def/MvFormalGroup_BasicV2.html#L52), i.e. invariant under swapping the two blocks of variables. Elements of [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162) are $d$-tuples of power series in variables indexed by $\mathbb{N}$, with zero constant terms, satisfying the compatibility of substitution into the Witt addition law `WittLaw.addFam p R` with addition along $\Phi$. Write $V$ for `verschiebungInt`, the additive endomorphism given by substituting the family `WittLaw.frobPolyFam`, $\langle a\rangle$ for the homothety `homothety a`, substitution of the Teichmüller family `teichFam a`, and $\mathrm{tangent}$ for the additive map sending $f$ to the $d$-tuple of coefficients of the degree-one monomial $X_0$ in the components of $f$. Given $f : \mathrm{Fin}\,d \to M$ such that the matrix with entries $\mathrm{tangent}(f_i)_j$ has invertible determinant, given $g \in M$ and given $N \in \mathbb{N}$, there is a unique pair $(c,h)$ with $c : \mathrm{Fin}\,N \to \mathrm{Fin}\,d \to R$ and $h \in M$ such that $$g = \sum_{m<N} V^m\Bigl(\sum_{i} \langle c_{m,i}\rangle f_i\Bigr) + V^N h.$$
--
--   This is the statement that a family of curves whose tangent vectors form a basis of $R^d$ is a $V$-basis of the Cartier module of $\Phi$, in the truncated form of expansions to finite order $N$ with an explicit remainder in $V^N M$; the base is any $\mathbb{Z}_p$-algebra, so no completeness or separatedness assumption on $R$ enters. It is used in the construction of formal $\mathcal{O}_D$-module data, where such expansions produce homomorphisms and structure constants from prescribed tangent behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add.lean

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

theorem MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra (PadicInt p) R]
    {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : IsUnit (Matrix.of fun i j => MvFormalGroup.CartierModule.tangent (f i) j).det)
    (g : MvFormalGroup.CartierModule p Φ) (N : ℕ) :
    ∃! ch : (Fin N → Fin d → R) × MvFormalGroup.CartierModule p Φ,
      g = (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
              (∑ i : Fin d, MvFormalGroup.CartierModule.homothety (ch.1 m i) (f i))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] ch.2 := by sorry
