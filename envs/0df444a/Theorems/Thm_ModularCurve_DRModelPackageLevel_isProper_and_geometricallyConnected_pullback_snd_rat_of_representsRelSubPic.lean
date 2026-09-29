-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isProper_and_geometricallyConnected_pullback_snd_rat_of_representsRelSubPic
-- name    : ModularCurve.DRModelPackageLevel.isProper_and_geometricallyConnected_pullback_snd_rat_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/95ec019d-58cf-5ceb-bc1b-c65ad555f7d9
-- title:
--   Properness and geometric connectedness of the generic Picard fibre
-- statement:
--   Fix an integer $N_0 \ge 1$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak{P}$ be a `DRModelPackageLevel N₀ p` datum for the Igusa scheme $X =$ `X N₀ p` with structure morphism `toBase N₀ p` $\colon X \to \operatorname{Spec}(R_p)$, that is, a record asserting that this morphism is proper, flat and locally of finite presentation with $X$ integral, that the sections of $X$ over affine opens are integrally closed, together with a curve model over $\overline{\mathbf{Q}}$ for the modular function field at level $N_0 p$ and its Galois- and chart-compatibilities, the smoothness of relative dimension one and geometric integrality of the base change of `toBase N₀ p` to $\mathbf{Q}$, and distinguished sections $\varepsilon_\infty$, $\varepsilon_0$ of `toBase N₀ p` (these data are summarised here). Let $D$ be a `RelativePic0Designation`, i.e. a scheme $D.P$ with a morphism $D.\mathrm{toBase} \colon D.P \to \operatorname{Spec}(R_p)$ and a section of it, and suppose $hD$ exhibits $D$ as representing the relative Picard presheaf rigidified along $\mathfrak{P}.\varepsilon_\infty$ and cut by the condition `algEquivZeroCut`: there is a rigidified invertible module (Poincaré bundle) on the fibre product of `toBase N₀ p` with $D.\mathrm{toBase}$ whose restriction to every geometric fibre is algebraically equivalent to zero, such that for every $R_p$-scheme $t \colon T \to \operatorname{Spec}(R_p)$ and every $\varepsilon_\infty$-rigidified invertible module on $X \times_{R_p} T$ with the same fibrewise algebraic-equivalence-to-zero property there is a unique $R_p$-morphism $T \to D.P$ pulling the Poincaré bundle back to it, the zero section corresponding to the unit bundle; assume further that $D.\mathrm{toBase}$ is locally of finite type. Then the projection $D.P \times_{\operatorname{Spec}(R_p)} \operatorname{Spec}(\mathbf{Q}) \to \operatorname{Spec}(\mathbf{Q})$, written as `pullback.snd` of $D.\mathrm{toBase}$ along the morphism induced by $R_p \to \mathbf{Q}$, is proper and geometrically connected.
--
--   This is the statement that the generic fibre of a relative $\mathrm{Pic}^0$ of the Deligne–Rapoport/Igusa model at level $N_0 p$ is a proper, geometrically connected $\mathbf{Q}$-scheme, i.e. the first half of the assertion that $J_0(N_0p)_{\mathbf{Q}}$ is an abelian variety. It is used in the construction of the Néron model data and the bridge statement for the relative Picard scheme of the fibre at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isProper_and_geometricallyConnected_pullback_snd_rat_of_representsRelSubPic.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian ModularCurve ModularCurve.DRLevel ModularCurve.IgusaScheme
open AlgebraicGeometry.RelPicard

theorem ModularCurve.DRModelPackageLevel.isProper_and_geometricallyConnected_pullback_snd_rat_of_representsRelSubPic
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    [LocallyOfFiniteType D.toBase] :
    IsProper (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) ∧
      GeometricallyConnected (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) := by sorry
