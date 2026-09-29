-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq
-- name    : ModularCurve.JZeroNeronObjectAtP.comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/02e24163-2f09-573e-bfc0-eb5e83e6f1ef
-- title:
--   Vanishing of the component map and sections over the inertia-invariant base
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$, $p$ prime and nonzero, and assume $p \nmid N_0$. Let $A$ be a valuation subring of $\overline{\mathbf Q}$ lying over $p$, in the sense that $p$ belongs to the nonunits of $A$, let $\Lambda$ be level data for $(N_0,p,A)$ and let $O$ be a Néron object `JZeroNeronObjectAtP` for these data, with structure morphism $g : G \to$ `base p`, relative group law, and bijection `pts` between $JZero(N_0p) = \mathrm{Pic}^0$ of the level-$N_0p$ modular function field over $\overline{\mathbf Q}$ and the set of sections of $g$ over the generic point. Let $x$ be an element of `inertiaInvariants A (N₀ * p)`, the subgroup of $JZero(N_0p)$ fixed by the inertia subgroup of $A$ in $\overline{\mathbf Q}/\mathbf Q$. Then the component invariant `O.comp x` vanishes if and only if there is a section $s$ of `RelativeGroupLaw.baseChangeStr Λ.shStr O.g`, that is, a morphism from `shBase A` $= \operatorname{Spec}$ `shRing A` to the pullback of $g$ along `Λ.shStr` whose composite with the projection to `shBase A` is the identity, such that the canonical lift `Λ.shGenLift (O.pts x)` of the generic point attached to $x$ equals `barPt A` followed by `shPt A`, followed by $s$.
--
--   This is the passage from the structural description of the kernel of the component map, which characterises it by extendability to an $A$-point of the Néron object, to the form needed in the gluing construction: vanishing of the component is equivalent to extendability of the corresponding point to a section over the inertia-invariant base `shBase A` of the base-changed scheme. It is used in the construction of the Néron glue, [`ModularCurve.JZeroNeronObjectAtP.exists_neronGlue`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_neronGlue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (x : ↥(inertiaInvariants A (N₀ * p))) :
    O.comp x = 0 ↔
      ∃ s : SchemeHomOver (𝟙 (shBase A)) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g),
        (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 = (barPt A ≫ shPt A) ≫ s.1 := by sorry
