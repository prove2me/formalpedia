-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_connectedComponentIn_baseChange_of_fst_eq_iotaFin
-- name    : ModularCurve.DRModelPackageLevel.mem_connectedComponentIn_baseChange_of_fst_eq_iotaFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/3ff11657-8e17-578f-9f1f-db6f0da5c260
-- title:
--   Chart points off v lie in the cusp component of geometric fibres
-- statement:
--   Fix $N_0\ge 1$ and a prime $q$ with $q\nmid N_0$, and let $\mathfrak P$ be a Deligne–Rapoport model package $\mathfrak P : \mathrm{DRModelPackageLevel}\ N_0\ q$ for the curve $X(N_0,q)$ over $R=R\,q$ with structure morphism `toBase`. Let $f\in R$ and let $v$ be an element of the finite-$j$ chart algebra $\mathrm{chartAlgFin}(N_0q,q)$, the subalgebra of the full modular function field of level $N_0q$ generated over $\mathbb Z_{(q)}$ in the $j$-chart. Assume the dictionary hypothesis on $v$: for every algebraically closed field $\kappa$ of characteristic $q$, every ring map $\mathrm{to}\kappa : R\to\kappa$, every point $y$ of the fibre $X(N_0,q)\times_{\mathrm{Spec}\,R}\mathrm{Spec}\,\kappa$ and every prime $\mathfrak q$ of the chart algebra, if the first projection carries $y$ to the point $\iota_{\mathrm{fin}}(\mathfrak q)$ and $v\notin\mathfrak q$, then $y$ lies in the image of $\mathfrak P.\mathrm{comp}\ \kappa\ \mathrm{to}\kappa\ 0$ and not in the image of $\mathfrak P.\mathrm{comp}\ \kappa\ \mathrm{to}\kappa\ 1$. Now let $k$ be an algebraically closed field, $s:\mathrm{Spec}\,k\to\mathrm{Spec}\,R[1/f]$ a geometric point of the localisation $\mathrm{Localization.Away}\ f$, and $y$ a point of the fibre over $s$ of the base change of `toBase` to $R[1/f]$. Let $\mathfrak q$ be a prime of the chart algebra with $v\notin\mathfrak q$ such that $\iota_{\mathrm{fin}}(\mathfrak q)$ lies in the open set $\mathfrak P.\mathrm{smoothLocus}$ of $X(N_0,q)$, and suppose the composite of the two first projections (fibre $\to$ base change $\to X(N_0,q)$) sends $y$ to $\iota_{\mathrm{fin}}(\mathfrak q)$. Then $y$ lies in the connected component, within the preimage of $\mathfrak P.\mathrm{smoothLocus}$ under that composite, of the image of the closed point of $\mathrm{Spec}\,k$ under the fibre point over $s$ of the base change to $R[1/f]$ of the section $\mathfrak P.\varepsilon_{\inf}$.
--
--   This is the fibrewise connectedness statement behind Ogg's description of the reduction of $X_0(N_0q)$ at $q$ as two copies of $X_0(N_0)$ meeting at the supersingular points: a chart point not annihilated by $v$, lying in the smooth locus, sits on the same connected component of the smooth trace as the cusp $\varepsilon_\infty$, uniformly over all geometric fibres of the base change to $R[1/f]$ (both residue characteristic $q$ and characteristic zero). It feeds the construction of one-sided pools in `exists_oneSidedPool_baseChange_of_levelPolynomials`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_mem_connectedComponentIn_baseChange_of_fst_eq_iotaFin.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve TensorProduct
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
open scoped Polynomial

namespace ModularCurve.DRModelPackageLevel

theorem mem_connectedComponentIn_baseChange_of_fst_eq_iotaFin
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) (f : R q)
    (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hdict : ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ)
      (y : ↥(fibre (N₀ := N₀) toκ)) (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)),
      (pullback.fst (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base y = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 →
      v ∉ 𝔮.asIdeal → y ∈ Set.range (𝔓.comp κ toκ 0).base ∧ y ∉ Set.range (𝔓.comp κ toκ 1).base)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
    (y : ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
    (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (hv : v ∉ 𝔮.asIdeal)
    (hsm : (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 ∈ (𝔓.smoothLocus : Set ↥(X N₀ q)))
    (hy : (pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫
        pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))).base y = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮) :
    y ∈ connectedComponentIn
        (((pullback.fst (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s ≫ pullback.fst (toBase N₀ q) (specMap (R q) (Localization.Away f))) ⁻¹ᵁ 𝔓.smoothLocus :
            (pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange (R q) (toBase N₀ q) (Localization.Away f)) s))
        (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔓.εinf) s).1).base (IsLocalRing.closedPoint k)) := by sorry
