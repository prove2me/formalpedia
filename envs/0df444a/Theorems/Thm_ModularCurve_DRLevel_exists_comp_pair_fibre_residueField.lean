-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_exists_comp_pair_fibre_residueField
-- name    : ModularCurve.DRLevel.exists_comp_pair_fibre_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/866f9d30-131a-56df-bc95-a18d4f2672c9
-- title:
--   Fibre of X₀(N₀q) at q: two closed-immersed copies
-- statement:
--   Fix $N_0 \ge 1$ and a prime $q$ with $q \nmid N_0$. The data are: a self-isomorphism $w$ of the scheme `DRLevel.X N₀ q` commuting with its structure morphism `DRLevel.toBase N₀ q` $=$ `IgusaScheme.igusaTo (N₀ * q) q` to $\operatorname{Spec}$ of the base ring `DRLevel.R q`; an `R q`-algebra automorphism $\theta$ of the finite-$j$ chart algebra `IgusaScheme.chartAlgFin (N₀ * q) q` which, read inside the function field `modularFunctionFieldFull (N₀ * q)`, is the restriction of `atkinLehnerInvolutionFull N₀ q`, together with the compatibility that `IgusaScheme.ιFin (N₀ * q) q` followed by $w$ equals $\operatorname{Spec}\theta$ followed by `IgusaScheme.ιFin (N₀ * q) q`; a morphism $\pi :$ `DRLevel.X N₀ q` $\to$ `DRLevel.X0 N₀ q` over `Spec (R q)`, and an `R q`-algebra map $\iota_0$ from `chartAlgFin N₀ q` to `chartAlgFin (N₀ * q) q` which is the identity on Laurent-series expansions, with `ιFin (N₀ * q) q` followed by $\pi$ equal to $\operatorname{Spec}\iota_0$ followed by `ιFin N₀ q`; and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ in its nonunits, with algebraically closed residue field of characteristic $q$ carrying decidable equality, and a ring map $\rho :$ `R q` $\to A$ compatible with the structure map to $\overline{\mathbb Q}$. Write $t$ for $\rho$ followed by the residue map. Then there are two morphisms $c_0, c_1$ from `DRLevel.fibre0 t` $=$ `X0 N₀ q` $\times_{\operatorname{Spec} R q} \operatorname{Spec}$(residue field) to `DRLevel.fibre t`, each commuting with the projections to $\operatorname{Spec}$ of the residue field, each a closed immersion, with every point of `fibre t` in the image of $c_0$ or of $c_1$, with the two point-set images distinct, with $c_0$ followed by `DRLevel.fibreMap0 π t` the identity, and with $c_0$ followed by `DRLevel.fibreMap w.hom hw t` equal to $c_1$.
--
--   This is the Deligne–Rapoport description of the geometric fibre at $q$ of the Igusa model of $X_0(N_0q)$ for $q \nmid N_0$: it is the union of two copies of the fibre of $X_0(N_0)$, the canonical section of the degeneracy map $\pi$ and its translate by the Atkin–Lehner involution $w_q$. It is the form of the statement in which the geometric point is given by a valuation subring of $\overline{\mathbb Q}$ lying over $q$, and it feeds [`ModularCurve.DRLevel.exists_comp_pair_fibre`](thm.html#ModularCurve.DRLevel.exists_comp_pair_fibre), which supplies the corresponding components of the Deligne–Rapoport model package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_exists_comp_pair_fibre_residueField.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.DRLevel IsLocalRing
open ModularCurve.IgusaScheme

theorem ModularCurve.DRLevel.exists_comp_pair_fibre_residueField
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q) (hw : w.hom ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (theta : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ≃ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (htheta : ∀ b, ((theta b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) =
      atkinLehnerInvolutionFull N₀ q (b : ↥(modularFunctionFieldFull (N₀ * q))))
    (hwchart : IgusaScheme.ιFin (N₀ * q) q ≫ w.hom =
      Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)

    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hiota : ∀ b, (((iota0 b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hpichart : IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ IgusaScheme.ιFin N₀ q)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]
    (ρ : DRLevel.R q →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)) :
    ∃ comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) ((residue ↥A).comp ρ) ⟶ DRLevel.fibre (N₀ := N₀) ((residue ↥A).comp ρ)),
      (∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _) ∧
      (∀ i, IsClosedImmersion (comp i)) ∧
      (∀ y : DRLevel.fibre (N₀ := N₀) ((residue ↥A).comp ρ), y ∈ Set.range (comp 0).base ∨ y ∈ Set.range (comp 1).base) ∧
      Set.range (comp 0).base ≠ Set.range (comp 1).base ∧
      comp 0 ≫ DRLevel.fibreMap0 π ((residue ↥A).comp ρ) = 𝟙 _ ∧
      comp 0 ≫ DRLevel.fibreMap w.hom hw ((residue ↥A).comp ρ) = comp 1 := by sorry
