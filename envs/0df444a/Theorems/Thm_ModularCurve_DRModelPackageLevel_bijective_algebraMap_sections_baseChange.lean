-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_bijective_algebraMap_sections_baseChange
-- name    : ModularCurve.DRModelPackageLevel.bijective_algebraMap_sections_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/ef17163d-3187-5fa8-a221-855a6539a40b
-- title:
--   Universal c_*𝒪=𝒪 for the level-N₀q Igusa model
-- statement:
--   Let $N_0$ be a nonzero natural number and $q$ a prime not dividing $N_0$, and let $\mathfrak P$ be a term of the structure `DRModelPackageLevel N₀ q hqN`, i.e. a Deligne–Rapoport-style package of data for the morphism `toBase N₀ q`, which is the Igusa structure morphism `IgusaScheme.igusaTo (N₀ * q) q` from the scheme `X N₀ q` to $\operatorname{Spec}$ of the base ring `R q` (the localisation of $\mathbf Z$ at the prime $(q)$); the package records that this morphism is proper, flat and locally of finite presentation with integral source, that sections over affine opens are integrally closed, a curve model over $\overline{\mathbf Q}$ whose function field is the modular function field of level $N_0q$ together with an isomorphism onto the geometric fibre and its compatibility with the arithmetic Galois action and with the chart expansions, smoothness of relative dimension $1$ and geometric integrality of the generic fibre, and cuspidal sections, among further data summarised here. The assertion is that for every commutative ring $A$ equipped with an `R q`-algebra structure, the global sections of the base change $\mathfrak X \times_{\operatorname{Spec} (R q)} \operatorname{Spec} A$, regarded as an $A$-algebra via the second projection of the pullback, are reached bijectively by the structure map: the algebra map $A \to \Gamma(\text{pullback of } \mathrm{toBase}\ N_0\ q \text{ along } \operatorname{Spec} A \to \operatorname{Spec}(R q),\ \top)$ is bijective.
--
--   This is the statement that $c_*\mathcal O = \mathcal O$ holds universally for the Deligne–Rapoport model of level $N_0q$ over $\mathbf Z_{(q)}$: the model has no extra global functions after any base change. It is used in the construction of the relative Picard functor data for this model, in [`ModularCurve.DRModelPackageLevel.exists_representsRelSubPic`](thm.html#ModularCurve.DRModelPackageLevel.exists_representsRelSubPic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_bijective_algebraMap_sections_baseChange.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve TensorProduct
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

namespace ModularCurve.DRModelPackageLevel

theorem bijective_algebraMap_sections_baseChange (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    ∀ (A : Type) [CommRing A] [Algebra (R q) A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd (toBase N₀ q) (Scheme.TwoAffineOpenCover.specMap (R q) A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback (toBase N₀ q) (Scheme.TwoAffineOpenCover.specMap (R q) A), ⊤)) := by sorry
