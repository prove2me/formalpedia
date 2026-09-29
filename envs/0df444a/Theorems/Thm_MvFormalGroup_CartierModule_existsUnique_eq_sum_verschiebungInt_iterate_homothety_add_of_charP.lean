-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add_of_charP
-- name    : MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/0d13bd37-e265-5caf-887f-04619751f74c
-- title:
--   Unique finite V-adic expansion in characteristic p
-- statement:
--   Let $p$ be a prime and $R$ a commutative ring of characteristic $p$, let $\Phi$ be a $d$-dimensional formal group law over $R$ — a $d$-tuple of power series in two families of $d$ variables with vanishing constant terms, linear coefficients $\delta_{ij}$ in each family, and associative — assumed commutative in the sense of `IsComm`. Consider the module `CartierModule p Φ` whose elements are $d$-tuples of power series in the variables $X_0,X_1,\dots$ with zero constant term which are additive for the Witt addition law, i.e. substituting the universal Witt addition polynomials reproduces $\Phi$-addition of the two substituted copies. Given $f : \mathrm{Fin}\,d \to$ `CartierModule p Φ` such that the matrix $\bigl(\mathrm{tangent}(f_i)_j\bigr)_{i,j}$, where $\mathrm{tangent}$ reads off the coefficient of $X_0$ in each component, has invertible determinant in $R$, and given $g$ in the Cartier module and $N \in \mathbb{N}$, the assertion is that there is a unique pair $(c,h)$ with $c : \mathrm{Fin}\,N \to \mathrm{Fin}\,d \to R$ and $h$ in the Cartier module satisfying $$g = \sum_{m<N} V^{m}\Bigl(\sum_{i} \langle c_{m,i}\rangle f_i\Bigr) + V^{N} h,$$ where $V$ is the $m$-fold iterate of the underlying function of `verschiebungInt`, substitution of the Frobenius-polynomial family of Witt endomorphisms, and $\langle a \rangle$ is `homothety a`, substitution of the Teichmüller family. Uniqueness is uniqueness of the pair of digits and remainder.
--
--   This is the characteristic-$p$ case of the $V$-adic expansion theorem of Cartier theory: an element of a Cartier module with a $V$-basis has a unique expansion into Teichmüller digits against the basis plus a remainder divisible by $V^N$. It is used in the study of formal $\mathcal{O}_D$-modules in the Čerednik–Drinfel'd setting, where it supplies structure constants and reduces equality of homomorphisms to their effect on a homogeneous $V$-basis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add_of_charP.lean

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

theorem MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add_of_charP
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
    {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : IsUnit (Matrix.of fun i j => MvFormalGroup.CartierModule.tangent (f i) j).det)
    (g : MvFormalGroup.CartierModule p Φ) (N : ℕ) :
    ∃! ch : (Fin N → Fin d → R) × MvFormalGroup.CartierModule p Φ,
      g = (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
              (∑ i : Fin d, MvFormalGroup.CartierModule.homothety (ch.1 m i) (f i))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] ch.2 := by sorry
