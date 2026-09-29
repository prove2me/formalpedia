-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_isNilpotent
-- name    : MvFormalGroup.CartierModule.verschiebungInt_injective_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/ff1423b1-0f70-53f6-802f-d07f753c7450
-- title:
--   Injectivity of Verschiebung when p is nilpotent
-- statement:
--   Let $p$ be a prime, $R$ a commutative ring in which the image of $p$ is nilpotent, $d$ a natural number, and $\Phi$ a $d$-dimensional formal group law over $R$: a $d$-tuple of power series $\Phi_i$ in the variables indexed by $\mathrm{Fin}\,d \sqcup \mathrm{Fin}\,d$ with vanishing constant term, whose linear coefficients in each block of variables are the identity matrix, and which satisfies the associativity identity in three blocks of variables; assume moreover $\Phi$ is commutative, i.e. swapping the two blocks of variables fixes each $\Phi_i$. The Cartier module $\mathtt{CartierModule}\ p\ \Phi$ consists of $d$-tuples $f = (f_j)$ of power series in variables indexed by $\mathbb{N}$, each with vanishing constant term, satisfying the homomorphism condition: substituting the Witt addition polynomials $\mathrm{addFam}\ p$ (the images over $R$ of the integral Witt polynomials $S_n$) into $f_j$ agrees with substituting the two families $(X_{(0,m)})$, $(X_{(1,m)})$ into the $j$-th component of $\Phi$ applied to $f$. The assertion is that the additive endomorphism $\mathtt{verschiebungInt}$ of this module, given by precomposing each $f_j$ with the family of integral Witt Frobenius polynomials $\mathrm{frobPolyFam}\ p\ R$, is injective as a map of underlying sets.
--
--   This is the injectivity of the Verschiebung operator $V$ on the module of $p$-typical curves of a commutative formal group law over a base in which $p$ is nilpotent, one of the defining conditions for a Cartier module to be reduced ($V$-torsion-free). It is used in the treatment of formal modules in the Čerednik–Drinfeld part of the development, in particular in the lemmas on $n$-torsion and on isogenies of special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_isNilpotent.lean

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

theorem MvFormalGroup.CartierModule.verschiebungInt_injective_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] (hp : IsNilpotent (p : R))
    {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Injective (MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)) := by sorry
