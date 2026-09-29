-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_inertiaInvariants_to_schemeHomOver_specGenericFibreInclusion_bijective
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_inertiaInvariants_to_schemeHomOver_specGenericFibreInclusion_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/842d87cc-fe02-57d6-86cd-022905fe35e7
-- title:
--   Inertia-invariant points as K_A-points of the base change
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime, and suppose $p \nmid N_0$. Let $A$ be a valuation subring of an algebraic closure $\overline{\mathbf Q}$ of $\mathbf Q$ lying over $p$, in the sense that the image of $p$ in $\overline{\mathbf Q}$ belongs to the non-units of $A$, let $\Lambda$ be level data for $(N_0,p,A)$ — a morphism $\sigma_A : \operatorname{Spec} A \to \operatorname{base} p$ compatible with the generic point, a scheme $X$ over $\operatorname{base} p$ carrying a relative group law, and bijections identifying $\mathrm{JZero}\,N_0$ with the points of $X$ over the generic point and the level-$N_0$ group over the residue field of $A$ with the points over the residue point — and let $O$ be a Néron object at $A$ of level $N_0 p$ over this level data, consisting of a scheme $G$ with structure morphism $g : G \to \operatorname{base} p$, a relative group law $O.L$ on $g$, a bijection $O.\mathrm{pts}$ from $\mathrm{JZero}\,(N_0 p)$ onto the points of $g$ over the generic point, together with the further commutativity, smoothness, separatedness, finite-type, quasi-compactness, surjectivity, fibre-connectedness, additivity, Galois-equivariance, Hecke, flatness and properness requirements of the structure (summarised here). Write $K_A = \mathrm{invField}\,A$ for the fixed field in $\overline{\mathbf Q}$ of the inertia subgroup $A.\mathrm{inertiaSubgroupIn}\ \mathbf Q$ and $O_A = \mathrm{shRing}\,A$ for the valuation subring of $K_A$ obtained by contracting $A$ along $K_A \hookrightarrow \overline{\mathbf Q}$. The assertion is that there exists a map $y_K$ from the subgroup $\mathrm{inertiaInvariants}\,A\,(N_0 p)$ of elements of $\mathrm{JZero}\,(N_0 p)$ fixed by that inertia subgroup to the set of morphisms $\operatorname{Spec} K_A \to G \times_{\operatorname{base} p} \operatorname{Spec} O_A$ lying over $\operatorname{Spec}$ of the inclusion $O_A \to K_A$, such that: composing $y_K(x)$ with $\operatorname{Spec}$ of the inclusion $K_A \to \overline{\mathbf Q}$ yields the base-changed $\overline{\mathbf Q}$-point $\Lambda.\mathrm{shGenLift}\,(O.\mathrm{pts}\,x)$; $y_K(x + x') = y_K(x) \cdot y_K(x')$ for the base-changed relative group law `(O.L.baseChange Λ.shStr).mul`; and $y_K$ is bijective.
--
--   This is the functor-of-points form of the dictionary $J(\overline{\mathbf Q})^{I_A} = J(K_A)$, identifying the inertia-invariant points of $J_0(N_0p)$ with the $K_A$-points of the base change of the Néron object along $\operatorname{Spec} O_A \to \operatorname{base} p$, compatibly with the group laws. It is used in the construction of sections over $\operatorname{Spec} O_A$ and in the gluing step for the Néron model, being cited by [`ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_section_specN_eq`](thm.html#ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_section_specN_eq) and [`ModularCurve.JZeroNeronObjectAtP.exists_neronGlue`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_neronGlue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_inertiaInvariants_to_schemeHomOver_specGenericFibreInclusion_bijective.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_inertiaInvariants_to_schemeHomOver_specGenericFibreInclusion_bijective
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    ∃ yK : ↥(inertiaInvariants A (N₀ * p)) →
        SchemeHomOver (specGenericFibreInclusion ↥(shRing A) ↥(invField A)) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g),
      (∀ x, Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫ (yK x).1 =
          (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1) ∧
      (∀ x x', yK (x + x') = (O.L.baseChange Λ.shStr).mul _ (yK x) (yK x')) ∧
      Function.Bijective yK := by sorry
