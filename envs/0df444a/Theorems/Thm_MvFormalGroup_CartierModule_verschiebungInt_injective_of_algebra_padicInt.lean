-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_algebra_padicInt
-- name    : MvFormalGroup.CartierModule.verschiebungInt_injective_of_algebra_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/6e77b43e-762d-504e-ba58-3545ab9ac5d8
-- title:
--   Injectivity of Verschiebung over a ℤₚ-algebra
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure, let $d$ be a natural number, and let $\Phi$ be a $d$-dimensional formal group law over $R$, i.e. a family $\Phi_i$ ($i \in \mathrm{Fin}\,d$) of power series in the variables indexed by $\mathrm{Fin}\,d \sqcup \mathrm{Fin}\,d$ with vanishing constant term, with linear coefficients $\delta_{ij}$ in each of the two groups of variables, and satisfying the associativity identity in $d$-tuples of power series in three groups of variables; assume moreover that $\Phi$ satisfies `IsComm`, that is, interchanging the two groups of variables fixes each $\Phi_i$. The object `CartierModule p Φ` consists of families $f_j$ ($j \in \mathrm{Fin}\,d$) of power series in variables indexed by $\mathbb{N}$, with vanishing constant term, which are additive for the Witt addition law: substituting the integral Witt addition polynomials $\mathrm{addFam}\,p$ into $f_j$ gives the result of substituting the two families obtained from $f$ by renaming the variables into the two argument slots of $\Phi_j$. The theorem asserts that the additive endomorphism `verschiebungInt` of `CartierModule p Φ`, defined as precomposition with the endomorphism of the Witt addition law given by the integral Frobenius family `frobPolyFam`, is injective as a function.
--
--   This is the injectivity of the Verschiebung operator $V$ on the Cartier module $\mathrm{Hom}(\widehat{W},\Phi)$ of a commutative formal group law over a $\mathbb{Z}_p$-algebra, one of the clauses of the reducedness properties of Cartier modules. It is used in the study of formal modules over orders in quaternion algebras occurring in the Čerednik–Drinfeld setting, for instance in the identification of the action of a uniformiser as a Teichmüller-twisted combination involving $V$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_algebra_padicInt.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.verschiebungInt_injective_of_algebra_padicInt
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra ℤ_[p] R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Injective (MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)) := by sorry
