-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_eq_of_forall_apply_nilEval_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.IsFormalCoordinates.eq_of_forall_apply_nilEval_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/acd6db41-7a7d-51c1-b50f-fa8ac8bea9c7
-- title:
--   Formal coordinates separate endomorphisms of a formal group
-- statement:
--   Let $B$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} B$ a morphism, and $L$ a relative group law on $f$: a group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of sections of $f$ over each $t : T \to \operatorname{Spec} B$, natural in $T$. Let $g \in \mathbb{N}$, let $F$ be a $g$-dimensional formal group law over $B$, and let $\theta$ be a formal coordinate datum for $f$: for every $B$-algebra $B'$ a map from $g$-tuples in $B'$ to sections of $f$ over $\operatorname{Spec} B' \to \operatorname{Spec} B$. Assume $\theta$ satisfies `IsFormalCoordinates` for $L$ and $F$, i.e. it is compatible with $B$-algebra maps on tuples of nilpotents, and for every $B$-algebra $B'$ and ideal $J$ with $J^{n+1} = 0$ it sends $J$-tuples to points congruent to the unit modulo $J$, is injective on $J$-tuples, hits every such infinitesimal point, and transports $F$'s truncated multiplication `nilMul` to `L.mul`. Let $\varepsilon, \varepsilon'$ be endomorphisms of $F$. Suppose that for every $B$-algebra $B'$, every ideal $J \subseteq B'$ with $J^{m+1} = \bot$, and every $s$ with all $s_i \in J$, the two points $\theta_{B'}\big(i \mapsto \mathrm{nilEval}\,m\,(\varepsilon_i)\,s\big)$ and $\theta_{B'}\big(i \mapsto \mathrm{nilEval}\,m\,(\varepsilon'_i)\,s\big)$ agree, where $\mathrm{nilEval}\,m\,\varphi\,s$ is the value at $s$ of the truncation of $\varphi$ in multidegree $(m,\dots,m)$. Then $\varepsilon = \varepsilon'$. Of the clauses of `IsFormalCoordinates`, the proof uses only injectivity on $J$-tuples.
--
--   This is the rigidity statement that an endomorphism of the formal group along the unit section of a relative group law is determined by the induced map on infinitesimal points of $A$: formal coordinates separate endomorphisms. It provides the uniqueness half of the dictionary between self-isogenies of a fake elliptic curve and formal germs, and is used in the construction of the endomorphism-action and character arguments for fake elliptic curves in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_eq_of_forall_apply_nilEval_eq.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.IsFormalCoordinates.eq_of_forall_apply_nilEval_eq
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    {g : ℕ} (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    (ε ε' : MvFormalGroup.End F)
    (h : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin g → B', (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval m (ε.toPowerSeries i) s) =
          θ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s)) :
    ε = ε' := by sorry
