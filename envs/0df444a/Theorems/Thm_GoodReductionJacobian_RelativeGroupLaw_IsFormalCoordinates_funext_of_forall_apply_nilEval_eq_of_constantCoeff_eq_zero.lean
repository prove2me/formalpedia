-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero
-- name    : GoodReductionJacobian.RelativeGroupLaw.IsFormalCoordinates.funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/a0690202-de01-523c-8c1b-185e6e6b44b8
-- title:
--   Formal coordinates separate tuples of series over B/I
-- statement:
--   Let $B$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} B$ a morphism, and let $L$ be a relative group law on $f$, that is, a functorial group structure (multiplication, unit, inverse, with associativity, unit laws, left inverse, and naturality under base change) on the sets of sections of $f$ over an arbitrary $B$-scheme. Let $F$ be a $g$-dimensional formal group law over $B$ and $\theta$ a system of formal coordinates, i.e. an assignment to each $B$-algebra $B'$ and each $g$-tuple $s$ in $B'$ of a section of $f$ over $\operatorname{Spec} B'$, and assume `L.IsFormalCoordinates F θ`: $\theta$ is natural along $B$-algebra maps for nilpotent tuples, and for every $B$-algebra $B'$ and ideal $J$ with $J^{m+1} = 0$ the map $\theta_{B'}$ carries $J$-tuples to points that reduce to the unit modulo $J$, is injective on $J$-tuples, has every such infinitesimal point in its image, and transports the truncated $F$-multiplication `F.nilMul m` to $L$'s multiplication. Let $I \subseteq B$ be an ideal and let $\sigma, \sigma'$ be $g$-tuples of power series in $g$ variables over $B/I$ with vanishing constant coefficients. Suppose that for every ring $B'$ carrying both a $(B/I)$-algebra and a $B$-algebra structure whose structure maps agree through $B \to B/I$, every ideal $J \subseteq B'$ and $m$ with $J^{m+1} = 0$, and every tuple $s$ with all $s_i \in J$, one has $\theta_{B'}\big((\text{nilEval}_m(\sigma_i)(s))_i\big) = \theta_{B'}\big((\text{nilEval}_m(\sigma'_i)(s))_i\big)$, where $\text{nilEval}_m(\varphi)(s)$ is the evaluation at $s$ of the truncation of $\varphi$ in degrees $\le m$ in each variable. Then $\sigma = \sigma'$.
--
--   A separation (rigidity) statement for formal coordinates: tuples of constant-term-free power series over a quotient $B/I$ of the base are determined by the points they define at all nilpotent test points over $(B/I)$-algebras, the form in which series representing maps between special fibres (the case $I = (\pi)$) are compared. It is used in the rigidification arguments for fake elliptic curves, where equalities of composites of series are deduced from equalities of the corresponding morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.IsFormalCoordinates.funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    {g : ℕ} (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    (I : Ideal B) (σ σ' : Fin g → MvPowerSeries (Fin g) (B ⧸ I))
    (hσ : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσ' : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0)
    (h : ∀ (B' : Type) [CommRing B'] [Algebra (B ⧸ I) B'] [Algebra B B'],
      algebraMap B B' = (algebraMap (B ⧸ I) B').comp (Ideal.Quotient.mk I) →
      ∀ (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin g → B', (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval m (σ i) s) = θ B' (fun i => MvFormalGroup.nilEval m (σ' i) s)) :
    σ = σ' := by sorry
