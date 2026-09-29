-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_existsUnique_section_comp_eq_pointEquivPlace_symm
-- name    : ModularCurve.DRModelPackageLevel.existsUnique_section_comp_eq_pointEquivPlace_symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/e48d9815-4271-5eae-9249-928351878b27
-- title:
--   Unique A-section of the model through a given place
-- statement:
--   Fix a nonzero natural number $N_0$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak P$ be a level-$N_0p$ Deligne–Rapoport model package for this data: a structure whose components make the Igusa morphism `toBase N₀ p` $\colon$ `X N₀ p` $\to \operatorname{Spec}(R\,p)$ proper, flat, locally of finite presentation with integral source and integrally closed sections over affine opens, and which supplies in addition a curve model $\mathfrak P.\mathrm{Meta}$ of the field `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbf Q}$ together with an isomorphism $\mathfrak P.\mathrm{eeta}$ from its underlying scheme onto the fibre product of `toBase N₀ p` with $\operatorname{Spec}$ of $R\,p \to \overline{\mathbf Q}$, compatible with the structure morphisms. Let $A$ be a valuation subring of $\overline{\mathbf Q}$, let $\rho \colon R\,p \to A$ be a ring homomorphism whose composition with the inclusion $A \hookrightarrow \overline{\mathbf Q}$ is the structure map $R\,p \to \overline{\mathbf Q}$, and let $V$ be a place of `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbf Q}$, that is, a proper valuation subring, a principal ideal ring, containing the image of $\overline{\mathbf Q}$. Through the curve model's bijection between places and sections of $\mathfrak P.\mathrm{Meta}.\mathrm{toBase}$, the place $V$ corresponds to a morphism $\operatorname{Spec}\overline{\mathbf Q} \to \mathfrak P.\mathrm{Meta}.C$; composing it with $\mathfrak P.\mathrm{eeta}$ and the first projection yields a $\overline{\mathbf Q}$-point $x_V$ of `X N₀ p`. The assertion is that there is exactly one pair consisting of a morphism $s \colon \operatorname{Spec} A \to$ `X N₀ p` with $s$ followed by `toBase N₀ p` equal to $\operatorname{Spec}(\rho)$, such that $\operatorname{Spec}(A \hookrightarrow \overline{\mathbf Q})$ followed by $s$ equals $x_V$.
--
--   This is the valuative criterion of properness (existence of the lift) together with separatedness (its uniqueness), applied to the Deligne–Rapoport model of the modular curve of level $N_0p$ over $R\,p$ and to a valuation subring $A$ of $\overline{\mathbf Q}$: every $\overline{\mathbf Q}$-point of the model, equivalently every place of the geometric function field, extends uniquely to an $A$-valued section. It is the mechanism by which points and divisors on the geometric fibre are specialised to sections of the model, and is used in the study of reductions of divisor classes and of the identity component of the associated Néron model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_existsUnique_section_comp_eq_pointEquivPlace_symm.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra IsLocalRing
  ModularCurve ModularCurve.DRLevel

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.existsUnique_section_comp_eq_pointEquivPlace_symm
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) :
    ∃! s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 =
        ((𝔓.Meta.pointEquivPlace).symm V).1 ≫ 𝔓.eeta ≫
          pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) := by sorry
