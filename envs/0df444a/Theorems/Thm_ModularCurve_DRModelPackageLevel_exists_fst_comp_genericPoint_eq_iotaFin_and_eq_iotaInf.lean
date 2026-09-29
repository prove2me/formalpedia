-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_fst_comp_genericPoint_eq_iotaFin_and_eq_iotaInf
-- name    : ModularCurve.DRModelPackageLevel.exists_fst_comp_genericPoint_eq_iotaFin_and_eq_iotaInf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/2a43e55c-99b5-5768-a58e-b1ed6d2b3299
-- title:
--   Generic points of both fibre components lie in both Igusa charts
-- statement:
--   Fix natural numbers $N_0$ and $q$ with $N_0 \neq 0$ and $q$ prime, and assume $q \nmid N_0$. Let $\mathfrak P$ be a Deligne–Rapoport package `DRModelPackageLevel N₀ q hqN` for the scheme `X N₀ q` over $\operatorname{Spec}$ of `DRLevel.R q`, let $\kappa$ be an algebraically closed field of characteristic $q$ with decidable equality, and let `toκ : DRLevel.R q →+* κ` be a ring homomorphism. Write `DRLevel.fibre0 toκ` for the pullback of `DRLevel.toBase0 N₀ q` along `Spec.map (CommRingCat.ofHom toκ)`, and assume it is an integral scheme; write `DRLevel.fibre toκ` for the pullback of `DRLevel.toBase N₀ q = IgusaScheme.igusaTo (N₀ * q) q` along the same morphism. For each $i \in \{0,1\}$ let `𝔓.comp κ toκ i` be the $i$-th component morphism `DRLevel.fibre0 toκ ⟶ DRLevel.fibre toκ` supplied by the package. The assertion is that, for both $i$, the image of the generic point of `DRLevel.fibre0 toκ` under `𝔓.comp κ toκ i` followed by `pullback.fst` (i.e. its image in `X N₀ q`) lies simultaneously in the range of `IgusaScheme.ιFin (N₀ * q) q` and in the range of `IgusaScheme.ιInf (N₀ * q) q`: there are prime ideals $\mathfrak q$ of the subalgebra `IgusaScheme.chartAlgFin (N₀ * q) q` (the chart attached to `jFull (N₀ * q)`) and $\mathfrak r$ of `IgusaScheme.chartAlgInf (N₀ * q) q` (the chart attached to `(jFull (N₀ * q))⁻¹`) whose images under the respective chart immersions equal that point.
--
--   In the Deligne–Rapoport description of the bad fibre of a modular curve at $q$, the characteristic-$q$ fibre is a union of two copies of the level-$N_0$ curve crossing at the supersingular points; this statement places the generic points of both copies inside each of the two charts of Igusa's scheme, so that both charts' coordinate rings act on the corresponding local rings. It is used in the orientation of the two components and in the identification of the stalk maps at these generic points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_fst_comp_genericPoint_eq_iotaFin_and_eq_iotaInf.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.exists_fst_comp_genericPoint_eq_iotaFin_and_eq_iotaInf
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
    [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)] :
    ∀ i : Fin 2,
      (∃ 𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q), (𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) =
        (IgusaScheme.ιFin (N₀ * q) q).base 𝔮) ∧
      (∃ 𝔯 : PrimeSpectrum ↥(IgusaScheme.chartAlgInf (N₀ * q) q), (𝔓.comp κ toκ i ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) =
        (IgusaScheme.ιInf (N₀ * q) q).base 𝔯) := by sorry
