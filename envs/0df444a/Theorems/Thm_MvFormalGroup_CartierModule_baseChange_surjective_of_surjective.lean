-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_baseChange_surjective_of_surjective
-- name    : MvFormalGroup.CartierModule.baseChange_surjective_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/b8766499-d1b4-5b4f-acc2-0f1e026d6d48
-- title:
--   Base change of Cartier modules along a surjection is surjective
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure, let $S$ be a commutative ring, and let $f \colon R \to S$ be a surjective ring homomorphism. Let $d$ be a natural number and let $\Phi$ be a $d$-dimensional formal group law over $R$, that is, a $d$-tuple of power series in two blocks $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ of variables with vanishing constant terms, whose linear coefficients in each block are the identity matrix and which satisfies the associativity identity; assume $\Phi$ is commutative, in the sense that each component is invariant under interchanging the two blocks of variables. The assertion is that the base-change map `baseChange` applied to $f$, from `CartierModule p Φ` to `CartierModule p (Φ.map f)`, is surjective as a map of underlying sets. Here an element of `CartierModule p Φ` is a $d$-tuple of power series in countably many variables indexed by $\mathbb{N}$, with vanishing constant terms, intertwining the Witt-vector addition law in $p$-typical form (substitution of the Witt addition polynomials `addFam p R`) with the group law $\Phi$ applied to the two blocks of variables; $\Phi.\mathrm{map}\ f$ is $\Phi$ with coefficients pushed forward along $f$, and the base-change map applies $f$ to all coefficients, `MvPowerSeries.map f` componentwise.
--
--   This is the surjectivity half of the first exact sequence of Cartier modules attached to a surjection of base rings, for the concrete Cartier module $\mathrm{Hom}(\hat W, \Phi)$ of a commutative formal group law: every homomorphism $\hat W \to \Phi_S$ over $S$ lifts to one over $R$. It is used in the Čerednik–Drinfeld part of the development, in the analysis of rigidified special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_baseChange_surjective_of_surjective.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem MvFormalGroup.CartierModule.baseChange_surjective_of_surjective
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra ℤ_[p] R] {S : Type v} [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Surjective
      (MvFormalGroup.CartierModule.baseChange (p := p) (Φ := Φ) f :
        MvFormalGroup.CartierModule p Φ → MvFormalGroup.CartierModule p (Φ.map f)) := by sorry
