-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_pow_eq_one_of_isInfinitesimal
-- name    : GoodReductionJacobian.RelativeGroupLaw.nsmul_pow_eq_one_of_isInfinitesimal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/9ecdd14f-da36-5c88-9f99-24e525ae7336
-- title:
--   Rigidity: N^μ kills J-infinitesimal points when N=0
-- statement:
--   Let $B$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} B$ a morphism carrying a relative group law $L$, that is, a functorial group structure (multiplication, unit, inverse, associativity, unit laws, left inverse, and naturality under base change) on the sets $\operatorname{SchemeHomOver}(t, f)$ of morphisms to $A$ over $f$ with fixed structure morphism $t$. Let $F$ be a $g$-variate formal group law over $B$ and let $\theta$ be a system of formal coordinates for $f$, i.e. for each $B$-algebra $B'$ a map sending a tuple in $(\mathrm{Fin}\,g \to B')$ to a point of $A$ over $\operatorname{Spec} B' \to \operatorname{Spec} B$; assume $L$.`IsFormalCoordinates` $F$ $\theta$ holds, meaning: $\theta$ is compatible with $B$-algebra maps applied to nilpotent tuples, and for every $B$-algebra $B'$, ideal $J$ and $n$ with $J^{n+1} = 0$, tuples with entries in $J$ are sent to points that are infinitesimal for $J$ (their reduction along $B' \to B'/J$ is the unit section), $\theta$ is injective on such tuples, every $J$-infinitesimal point is $\theta$ of such a tuple, and $\theta(F.\mathrm{nilMul}\,n\,s\,t) = \theta(s)\cdot\theta(t)$, where `nilMul` is truncated evaluation of the power series of $F$. Let $B'$ be a $B$-algebra, $N$ a natural number with $N = 0$ in $B'$, $J \subseteq B'$ an ideal and $\mu$ with $J^{\mu+1} = \bot$, and let $P$ be a point of $A$ over $\operatorname{Spec} B' \to \operatorname{Spec} B$ that is infinitesimal for $J$. Then the $N^{\mu}$-fold iterated product of $P$ under $L$ equals the unit section over $\operatorname{Spec} B'$.
--
--   This is the rigidity statement, in the form used by Katz and Drinfeld, that a point congruent to the unit section modulo a nilpotent ideal $J$ with $J^{\mu+1}=0$ is annihilated by $N^{\mu}$ whenever the integer $N$ vanishes in the base. It supplies the torsion bound used in the smooth-case variant [`GoodReductionJacobian.RelativeGroupLaw.nsmul_pow_eq_one_of_isInfinitesimal_of_smooth`](thm.html#GoodReductionJacobian.RelativeGroupLaw.nsmul_pow_eq_one_of_isInfinitesimal_of_smooth) and in the extraction of a uniform annihilator, [`GoodReductionJacobian.RelativeGroupLaw.exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_pow_eq_one_of_isInfinitesimal.lean

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_pow_eq_one_of_isInfinitesimal
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    {g : ℕ} (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    {B' : Type} [CommRing B'] [Algebra B B'] (N : ℕ) (hN : (N : B') = 0)
    (J : Ideal B') (μ : ℕ) (hJ : J ^ (μ + 1) = ⊥)
    (P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f) (hP : L.IsInfinitesimal J P) :
    L.nsmul (Scheme.specOver (𝒪 := B) B') (N ^ μ) P = L.one (Scheme.specOver (𝒪 := B) B') := by sorry
