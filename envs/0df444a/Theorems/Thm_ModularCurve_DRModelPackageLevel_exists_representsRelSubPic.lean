-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_representsRelSubPic
-- name    : ModularCurve.DRModelPackageLevel.exists_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/b77610df-489e-503d-a823-edf831996c65
-- title:
--   Representability of relative Pic⁰ of the level-N₀q model
-- statement:
--   Let $N_0\ge 1$ be a natural number, $q$ a prime with $q\nmid N_0$, and let $\mathfrak P$ be an inhabitant of `DRModelPackageLevel N₀ q hqN`, the structure bundling the data and properties of the project's Deligne–Rapoport model: the structure morphism `DRLevel.toBase N₀ q` from the glued scheme `X N₀ q` to $\operatorname{Spec}$ of the ring `DRLevel.R q` is proper, flat and locally of finite presentation, `X N₀ q` is integral with integrally closed sections on affine opens, its base change to $\overline{\mathbb Q}$ is identified with a smooth proper curve model of the modular function field of level $N_0q$, compatibly with the Galois action and pinned on the Igusa chart, the generic fibre is smooth of relative dimension $1$ and geometrically integral, and distinguished sections $\varepsilon_\infty,\varepsilon_0$ over $\operatorname{Spec}$ `DRLevel.R q` are given. The assertion is that there exist a scheme $D.P$ with a morphism $D.\mathrm{toBase}\colon D.P\to\operatorname{Spec}$ `DRLevel.R q` and a section of it (a `RelativePic0Designation`), together with a `RepresentsRelSubPic` datum for the $\varepsilon_\infty$-rigidified relative Picard functor of `DRLevel.toBase N₀ q` cut out by `algEquivZeroCut`: a rigidified invertible module (Poincaré bundle) on the pullback of `DRLevel.toBase N₀ q` along $D.\mathrm{toBase}$ whose restriction to each geometric fibre is algebraically equivalent to zero, such that for every $t\colon T\to\operatorname{Spec}$ `DRLevel.R q` and every $\varepsilon_\infty$-rigidified invertible module on the pullback of `DRLevel.toBase N₀ q` along $t$ that is algebraically equivalent to zero on every geometric fibre there is a unique morphism $T\to D.P$ over the base pulling the Poincaré bundle back to it, and the pullback of the Poincaré bundle along the zero section is isomorphic to the unit; moreover $D.\mathrm{toBase}$ is smooth, separated, quasi-compact, surjective and geometrically connected.
--
--   This is the representability of the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model at level $N_0q$ over $\mathbb Z_{(q)}$, i.e. the identity component of the Néron model of $J_0(N_0q)$ at $q$, obtained as a pointed smooth separated group-scheme-shaped object with geometrically connected fibres. It feeds [`ModularCurve.DRModelPackageLevel.exists_jZeroNeronObjectAtP_and_bridge_representsRelSubPic_abqFibre_of_levelModel`](thm.html#ModularCurve.DRModelPackageLevel.exists_jZeroNeronObjectAtP_and_bridge_representsRelSubPic_abqFibre_of_levelModel), where the Jacobian's Néron model data at $q$ is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_representsRelSubPic.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicCurve
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
namespace ModularCurve.DRModelPackageLevel

theorem exists_representsRelSubPic (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    ∃ D : RelativePic0Designation (DRLevel.R q) (DRLevel.toBase N₀ q),
      Nonempty (RepresentsRelSubPic (DRLevel.toBase N₀ q) 𝔓.εinf (algEquivZeroCut (DRLevel.toBase N₀ q) 𝔓.εinf) D) ∧
        Smooth D.toBase ∧ IsSeparated D.toBase ∧ QuasiCompact D.toBase ∧
        Surjective D.toBase ∧ GeometricallyConnected D.toBase := by sorry
