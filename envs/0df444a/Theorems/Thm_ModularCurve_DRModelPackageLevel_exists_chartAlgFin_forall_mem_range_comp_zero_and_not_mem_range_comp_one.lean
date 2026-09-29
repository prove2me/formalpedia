-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one
-- name    : ModularCurve.DRModelPackageLevel.exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/a894822f-311b-5e58-a318-e6983117ff0b
-- title:
--   An Ogg unit separating the two components of the q-fibre
-- statement:
--   Let $N_0\ge 1$ and let $q$ be a prime with $q\nmid N_0$, and let $\mathfrak P$ be a term of the Deligne–Rapoport package structure `DRModelPackageLevel N₀ q hqN` for the scheme `DRLevel.X N₀ q` over $\operatorname{Spec}$ of `DRLevel.R q` via `DRLevel.toBase N₀ q = IgusaScheme.igusaTo (N₀ * q) q`. The assertion is the existence of an element $v$ of the subalgebra `IgusaScheme.chartAlgFin (N₀ * q) q` (that is, `chartAlg (N₀ * q) q {jFull (N₀ * q)}`, a subalgebra over [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) of the modular function field `modularFunctionFieldFull (N₀ * q)`, the intermediate field of $\mathbb Q((\mathfrak q))$ generated over $\mathbb Q$ by the divisor expansions) with two properties. First, the Laurent series over $\mathbb Q$ underlying $v$ is either `modularUnitSeries q`, namely `deltaSeries * (deltaSeriesN q)⁻¹`, or the product of the constant $q^{12}$ with its inverse. Second, for every field $\kappa$ of characteristic $q$ that is algebraically closed, every ring homomorphism $\mathrm{to}\kappa\colon$ `DRLevel.R q` $\to\kappa$, every point $y$ of the fibre `DRLevel.fibre toκ`, the pullback of `DRLevel.toBase N₀ q` along `Spec.map (CommRingCat.ofHom toκ)`, and every prime ideal $\mathfrak q$ of `IgusaScheme.chartAlgFin (N₀ * q) q`: if the image of $y$ under the underlying map of the first projection of that pullback coincides with the image of $\mathfrak q$ under the underlying map of the chart morphism `IgusaScheme.ιFin (N₀ * q) q`, and $v\notin\mathfrak q$, then $y$ lies in the range of the underlying map of $\mathfrak P.\mathrm{comp}\ \kappa\ \mathrm{to}\kappa\ 0$ and does not lie in the range of the underlying map of $\mathfrak P.\mathrm{comp}\ \kappa\ \mathrm{to}\kappa\ 1$.
--
--   This is the dictionary between Ogg's modular unit $\Delta(\mathfrak q)/\Delta(\mathfrak q^{q})$ on the finite-$j$ chart of the level-$N_0q$ model over $\mathbb Z_{(q)}$ and the two components of its characteristic-$q$ fibre: on the non-vanishing locus of the unit one is on the component indexed $0$ and off the component indexed $1$, hence away from the crossings. It is used in the construction of the two-sided pools of closed primes in the smooth locus of the bad fibre, and in the statement about stalks at a crossing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

namespace ModularCurve.DRModelPackageLevel

theorem exists_chartAlgFin_forall_mem_range_comp_zero_and_not_mem_range_comp_one
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    ∃ v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ((((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = modularUnitSeries q) ∨
        (((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = (q : LaurentSeries ℚ) ^ 12 * (modularUnitSeries q)⁻¹)) ∧
      ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
        (y : ↥(DRLevel.fibre (N₀ := N₀) toκ)) (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)),
        (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base y = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 →
        v ∉ 𝔮.asIdeal →
        y ∈ Set.range (𝔓.comp κ toκ 0).base ∧ y ∉ Set.range (𝔓.comp κ toκ 1).base := by sorry
