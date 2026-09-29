-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFormalCoordinates_baseChange
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isFormalCoordinates_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/58a72b18-bad9-5e84-a32a-f9ab5a6be471
-- title:
--   Formal coordinates are stable under base change
-- statement:
--   Let $B$ and $B'$ be commutative rings and let $\iota : \operatorname{Spec} B' \to \operatorname{Spec} B$ be a morphism of affine schemes, with underlying ring map $(\mathtt{Spec.preimage}\ \iota).\mathrm{hom} : B \to B'$. Let $f : A \to \operatorname{Spec} B$ be a morphism of schemes carrying a relative group law $L$, that is, a group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections of $f$ over each $t : T \to \operatorname{Spec} B$, natural in $t$ under precomposition. Let $d \in \mathbb{N}$, let $F$ be a $d$-dimensional multivariate formal group law over $B$ (a $d$-tuple of power series in $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ variables with vanishing constant term, identity linear terms and the associativity identity), and let $\theta$ assign to every $B$-algebra $B''$ and every tuple $s : \mathrm{Fin}\,d \to B''$ a point $\operatorname{Spec} B'' \to A$ over $\operatorname{Spec} B$. Assume $L.\mathrm{IsFormalCoordinates}\ F\ \theta$: $\theta$ commutes with $B$-algebra maps on nilpotent tuples, and for every $B$-algebra $B''$, every ideal $J$ with $J^{n+1} = 0$, the map $s \mapsto \theta(s)$ on tuples with entries in $J$ takes values in the points whose reduction modulo $J$ is the unit, is injective, is onto those points, and carries the $n$-truncated evaluation of $F$ to the multiplication of $L$. Then there exist formal coordinates $\theta'$ of dimension $d$ for the base-changed structure morphism $\mathrm{pr}_2 : A \times_{\operatorname{Spec} B} \operatorname{Spec} B' \to \operatorname{Spec} B'$ such that $\theta'$ are formal coordinates for the base-changed group law $L.\mathrm{baseChange}\ \iota$ with respect to the formal group law obtained from $F$ by applying $B \to B'$ to coefficients, and such that for every $B'$-algebra $C$, regarded as a $B$-algebra through $B \to B' \to C$, and every $s : \mathrm{Fin}\,d \to C$, the morphism underlying $\theta'\,C\,s$ followed by $\mathrm{pr}_1 : A \times_{\operatorname{Spec} B} \operatorname{Spec} B' \to A$ equals the morphism underlying $\theta\,C\,s$.
--
--   This is the base-change compatibility of formal coordinates along the unit section of a relative group law: coordinates over $B$ transport to coordinates over $B'$ for the pulled-back law, compatibly with the projection to $A$. It is used to pass to fibres, for instance in deducing that a morphism admitting formal coordinates of dimension $d$ is smooth of relative dimension $d$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFormalCoordinates_baseChange.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isFormalCoordinates_baseChange
    {B B' : Type} [CommRing B] [CommRing B']
    (ι : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of B))
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    {d : ℕ} (F : MvFormalGroup d B) (θ : RelativeGroupLaw.FormalCoordinates f d) (hθ : L.IsFormalCoordinates F θ) :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates (RelativeGroupLaw.baseChangeStr ι f) d,
      (L.baseChange ι).IsFormalCoordinates (F.map (Spec.preimage ι).hom) θ' ∧
      ∀ (C : Type) [CommRing C] [Algebra B' C] (s : Fin d → C),
        letI : Algebra B C := ((algebraMap B' C).comp (Spec.preimage ι).hom).toAlgebra
        (θ' C s).1 ≫ pullback.fst f ι = (θ C s).1 := by sorry
