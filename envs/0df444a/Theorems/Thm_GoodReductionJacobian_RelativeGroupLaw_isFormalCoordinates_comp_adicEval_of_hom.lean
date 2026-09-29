-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFormalCoordinates_comp_adicEval_of_hom
-- name    : GoodReductionJacobian.RelativeGroupLaw.isFormalCoordinates_comp_adicEval_of_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/d467e468-a435-5c4a-85e1-fb2804115060
-- title:
--   Formal coordinates transported along an isomorphism of formal groups
-- statement:
--   Let $B$ be a commutative ring, let $f : A \to \operatorname{Spec} B$ be a morphism of schemes and let $L$ be a relative group law on $f$, i.e. a group structure on the sets $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of sections over each $t : T \to \operatorname{Spec} B$, natural in $T$. Let $g \in \mathbb{N}$, let $F$ and $G$ be $g$-dimensional formal group laws over $B$, and let $\theta$ be a system of formal coordinates for $f$: an assignment, for each $B$-algebra $B'$ and each tuple $s : \mathrm{Fin}\ g \to B'$, of a section of $f$ over $\operatorname{Spec} B'$. Assume `L.IsFormalCoordinates F θ`, that is: $\theta$ is natural in $B'$ along $B$-algebra maps when evaluated at nilpotent tuples, and for every ideal $J$ of a $B$-algebra $B'$ with $J^{n+1} = 0$, the points $\theta(s)$ for $s \in J^g$ are exactly the points congruent to the unit section modulo $J$, each arising from a unique such $s$, and $\theta(F.\mathrm{nilMul}\ n\ s\ t) = L.\mathrm{mul}(\theta(s), \theta(t))$, where $F.\mathrm{nilMul}$ evaluates the truncations of the power series of $F$. Let $\Phi : G \to F$ and $\Psi : F \to G$ be homomorphisms of formal group laws with $\Psi \circ \Phi = \mathrm{id}_G$ and $\Phi \circ \Psi = \mathrm{id}_F$. The conclusion is twofold: first, the family sending $s : \mathrm{Fin}\ g \to C$ to $\theta_C\bigl(i \mapsto \mathrm{adicEval}\ (\mathrm{span}\,(\mathrm{range}\ s))\ s\ (\Phi_i)\bigr)$ is a system of formal coordinates for $f$ whose group law is $G$; second, for every $B$-algebra $C$, ideal $J \subseteq C$ and $n$ with $J^{n+1} = \bot$, and every tuple $s$ with all entries in $J$, this adic evaluation of the power series of $\Phi$ at $s$ may be replaced, inside $\theta$, by the finite evaluation $\mathrm{nilEval}\ n$ of the degreewise truncations.
--
--   This is the statement that a system of formal coordinates along the unit section of a relative group law may be re-coordinatised by an isomorphism of formal group laws, the resulting coordinates having the source law as their group law, together with the comparison of adic and truncated evaluation on nilpotent tuples. It is used to re-coordinatise deformations so that the induced law becomes a prescribed one, in the construction of fake elliptic curves and in the existence of deformations with prescribed formal coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isFormalCoordinates_comp_adicEval_of_hom.lean

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_MvFormalGroup_PointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isFormalCoordinates_comp_adicEval_of_hom
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) {g : ℕ} (F G : MvFormalGroup g B)
    (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    (Φ : MvFormalGroup.Hom G F) (Ψ : MvFormalGroup.Hom F G)
    (hΨΦ : Ψ.comp Φ = MvFormalGroup.Hom.id G) (hΦΨ : Φ.comp Ψ = MvFormalGroup.Hom.id F) :
    L.IsFormalCoordinates G
        (fun (C : Type) _ _ (s : Fin g → C) =>
          θ C (fun i => MvFormalGroup.adicEval (Ideal.span (Set.range s)) s (Φ.toPowerSeries i))) ∧
      ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin g → C, (∀ i, s i ∈ J) →
          θ C (fun i => MvFormalGroup.adicEval (Ideal.span (Set.range s)) s (Φ.toPowerSeries i)) =
            θ C (fun i => MvFormalGroup.nilEval n (Φ.toPowerSeries i) s) := by sorry
