-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hom_apply_eq_apply_nilEval_of_isFormalCoordinates
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_hom_apply_eq_apply_nilEval_of_isFormalCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/f41a9a41-7b08-5094-a6f9-e5778b4918b6
-- title:
--   Change of formal coordinates at the unit section
-- statement:
--   Let $B$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} B$, and let $L$ be a relative group law on $f$, that is, a group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-points over each $t : T \to \operatorname{Spec} B$, compatible with base change along $T' \to T$. Let $g \in \mathbb{N}$, let $F, F'$ be $g$-dimensional commutative-ring formal group laws over $B$ (given by $g$ power series in $2g$ variables satisfying the normalisation and associativity identities), and let $\theta, \theta'$ assign, to each $B$-algebra $B'$ and each tuple $s : \mathrm{Fin}\,g \to B'$, a section of $f$ over $\operatorname{Spec} B'$. Assume $\theta$ is a system of formal coordinates for $L$ with associated law $F$, and $\theta'$ one with associated law $F'$: each is natural in $B$-algebra maps on nilpotent tuples, and for every ideal $J$ of a $B$-algebra $B'$ with $J^{n+1} = 0$ it sends tuples with entries in $J$ bijectively onto the sections congruent to the unit modulo $J$ and carries the truncated group law of $F$ (resp. $F'$) to $L$'s multiplication. The conclusion asserts the existence of a homomorphism of formal group laws $\varphi : F \to F'$ (a $g$-tuple of power series in $g$ variables with zero constant terms intertwining the two laws) such that: there is $\psi : F' \to F$ with $\psi \circ \varphi = \mathrm{id}_F$ and $\varphi \circ \psi = \mathrm{id}_{F'}$; for every $B$-algebra $B''$, every ideal $J \subseteq B''$ and $n$ with $J^{n+1} = 0$, and every tuple $s$ with entries in $J$, one has $\theta_{B''}(s) = \theta'_{B''}\bigl(i \mapsto \mathrm{nilEval}_n(\varphi_i)(s)\bigr)$, where $\mathrm{nilEval}_n$ evaluates the truncation of a power series in degrees $\le n$ in each variable; and $\varphi$ is the unique homomorphism $F \to F'$ with this last property.
--
--   This is the classical comparison of two systems of formal coordinates along the unit section of a group scheme: they differ by a unique isomorphism of the associated formal group laws. It is used in the deformation-theoretic results [`GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates`](thm.html#GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates) and [`GoodReductionJacobian.BareDeformation.isIso_of_isFormalCoordinates_of_liftsCoordinates`](thm.html#GoodReductionJacobian.BareDeformation.isIso_of_isFormalCoordinates_of_liftsCoordinates), where the formal group attached to a relative group law must be identified independently of the chosen coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hom_apply_eq_apply_nilEval_of_isFormalCoordinates.lean

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_hom_apply_eq_apply_nilEval_of_isFormalCoordinates
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) {g : ℕ} (F F' : MvFormalGroup g B)
    (θ θ' : RelativeGroupLaw.FormalCoordinates f g)
    (hθ : L.IsFormalCoordinates F θ) (hθ' : L.IsFormalCoordinates F' θ') :
    ∃ φ : MvFormalGroup.Hom F F',
      (∃ ψ : MvFormalGroup.Hom F' F, ψ.comp φ = MvFormalGroup.Hom.id F ∧ φ.comp ψ = MvFormalGroup.Hom.id F') ∧
      (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin g → B'', (∀ i, s i ∈ J) →
          θ B'' s = θ' B'' (fun i => MvFormalGroup.nilEval n (φ.toPowerSeries i) s)) ∧
      ∀ φ₂ : MvFormalGroup.Hom F F',
        (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin g → B'', (∀ i, s i ∈ J) →
            θ B'' s = θ' B'' (fun i => MvFormalGroup.nilEval n (φ₂.toPowerSeries i) s)) → φ₂ = φ := by sorry
