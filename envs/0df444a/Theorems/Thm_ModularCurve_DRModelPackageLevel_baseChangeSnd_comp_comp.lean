-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_baseChangeSnd_comp_comp
-- name    : ModularCurve.DRModelPackageLevel.baseChangeSnd_comp_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/c929653f-2fc3-550a-addc-4fc73023f6ee
-- title:
--   Twists of the geometric point commute with the component maps
-- statement:
--   Fix a natural number $N_0 \neq 0$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak{P}$ be an inhabitant of `DRModelPackageLevel N₀ q hqN`, the structure bundling the Deligne–Rapoport data for the Igusa scheme `X N₀ q` over $\operatorname{Spec} R$, $R =$ `DRLevel.R q` (properness, flatness, integrality and local finite presentation of the structure morphism `toBase N₀ q` $=$ `IgusaScheme.igusaTo (N₀ * q) q`, normality on affine opens, a curve model over $\overline{\mathbb{Q}}$ with its Galois- and $q$-expansion compatibilities, smoothness and geometric integrality of the generic fibre, the sections $\varepsilon_\infty,\varepsilon_0$, and further data including the component morphisms used below). Let $\kappa$ be an algebraically closed field of characteristic $q$ that is an $R$-algebra, let $\tau$ be an endomorphism of $\operatorname{Spec}\kappa$ over $\operatorname{Spec} R$, that is, a morphism $\tau \colon \operatorname{Spec}\kappa \to \operatorname{Spec}\kappa$ whose composite with `SmoothProperCurve.specMap (DRLevel.R q) κ` is again that structure morphism, and let $i \in \{0,1\}$. Writing $1 \times \tau$ for `RelPicard.baseChangeSnd c τ`, the morphism $\mathrm{pullback}(c,\,\mathrm{specMap}) \to \mathrm{pullback}(c,\,\mathrm{specMap})$ given by the identity on the first factor and $\tau$ on the second, the assertion is that $1 \times \tau$ for $c =$ `toBase0 N₀ q` $=$ `IgusaScheme.igusaTo N₀ q` followed by the $i$-th component morphism $\mathfrak{P}.\mathrm{comp}\,\kappa\,(\text{algebraMap } R\ \kappa)\,i \colon X_0 \times_R \operatorname{Spec}\kappa \to X \times_R \operatorname{Spec}\kappa$ equals that component morphism followed by $1 \times \tau$ for $c =$ `toBase N₀ q`.
--
--   This is the equivariance (descent) datum for the two components of the fibre at $q$ of the Deligne–Rapoport model of $X_0(N_0q)$: each component morphism commutes with every endomorphism of the geometric point $\operatorname{Spec}\kappa$ over $\operatorname{Spec}\mathbb{Z}_{(q)}$, Frobenius in particular. It is shaped so as to match the commutation hypothesis required when comparing base-changed relative Picard schemes, and is used in the analysis of the Néron model of the Jacobian of $X_0(N_0q)$ at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_baseChangeSnd_comp_comp.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
namespace ModularCurve.DRModelPackageLevel

theorem baseChangeSnd_comp_comp (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] [Algebra (DRLevel.R q) κ]
    (τ : SchemeHomOver (SmoothProperCurve.specMap (DRLevel.R q) κ) (SmoothProperCurve.specMap (DRLevel.R q) κ)) (i : Fin 2) :
    RelPicard.baseChangeSnd (DRLevel.toBase0 N₀ q) τ ≫ 𝔓.comp κ (algebraMap (DRLevel.R q) κ) i =
      𝔓.comp κ (algebraMap (DRLevel.R q) κ) i ≫ RelPicard.baseChangeSnd (DRLevel.toBase N₀ q) τ := by sorry
