-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_exists_cusps_involution_forgetful_smoothLocus
-- name    : ModularCurve.DRLevel.exists_cusps_involution_forgetful_smoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/0c92fd0d-96c9-5acf-8e31-a4c0de089943
-- title:
--   Cusps, Atkin–Lehner involution, degeneracy map and smooth locus
-- statement:
--   Let $N_0\ge 1$ and let $q$ be a prime with $q\nmid N_0$. Write $R =$ `DRLevel.R q` for the base ring (which carries a coercion to $\mathbb{Q}$), $\mathfrak{X} =$ `DRLevel.X N₀ q` for the Igusa scheme at level $N_0q$ — the pushout of the spectra of the two chart algebras `chartAlgFin (N₀ * q) q` and `chartAlgInf (N₀ * q) q`, the $R$-subalgebras of elements of the field `modularFunctionFieldFull (N₀ * q)` $\subseteq \mathbb{Q}((T))$ integral over $R[j]$, resp. over $R[j^{-1}]$ — with structure morphism `DRLevel.toBase N₀ q` to $\operatorname{Spec}R$, and similarly $\mathfrak{X}_0$ with `DRLevel.toBase0 N₀ q` at level $N_0$. Then there exist: two sections $\varepsilon_\infty,\varepsilon_0$ of `DRLevel.toBase N₀ q` (morphisms $\operatorname{Spec}R\to\mathfrak{X}$ whose composite with the structure morphism is the identity); an $R$-algebra map $\rho_\infty$ from `chartAlgInf (N₀ * q) q` to $R$; an isomorphism $w$ of $\mathfrak{X}$; an $R$-algebra automorphism $\theta$ of `chartAlgFin (N₀ * q) q`; a morphism $\pi\colon\mathfrak{X}\to\mathfrak{X}_0$ over $\operatorname{Spec}R$; $R$-algebra maps $\iota_0$, $\iota_\infty$ from the level-$N_0$ finite and pole chart algebras into the corresponding level-$N_0q$ ones; and an open $U\subseteq\mathfrak{X}$ together with a witness that $U\hookrightarrow\mathfrak{X}\to\operatorname{Spec}R$ is smooth of relative dimension $1$, such that: $\rho_\infty(b)$, viewed in $\mathbb{Q}$, is the zeroth Laurent coefficient of $b$ for all $b$, and $\varepsilon_\infty$ is $\operatorname{Spec}\rho_\infty$ followed by the pole-chart morphism `ιInf (N₀ * q) q`; $w$ commutes with the structure morphism, $w\circ w=\mathrm{id}$, and $\varepsilon_\infty$ followed by $w$ equals $\varepsilon_0$; $\theta$ induces on the function field the automorphism `atkinLehnerInvolutionFull N₀ q`, i.e. the chosen $\mathbb{Q}$-automorphism of `modularFunctionFieldFull (N₀ * q)` interchanging the expansions of $j$ at $d$ and at $dq$ for every divisor $d$ of $N_0$ when such an automorphism exists and the identity otherwise, and `ιFin (N₀ * q) q` followed by $w$ equals $\operatorname{Spec}\theta$ followed by `ιFin (N₀ * q) q`; $\iota_0$ and $\iota_\infty$ preserve Laurent expansions, and `ιFin (N₀ * q) q`, resp. `ιInf (N₀ * q) q`, followed by $\pi$ equals $\operatorname{Spec}\iota_0$, resp. $\operatorname{Spec}\iota_\infty$, followed by the corresponding level-$N_0$ chart morphism; and finally every open $V$ with $V\hookrightarrow\mathfrak{X}\to\operatorname{Spec}R$ smooth satisfies $V\le U$, while the images of $\varepsilon_\infty$ and $\varepsilon_0$ lie in $U$.
--
--   This packages the standard structural features of the Deligne–Rapoport/Katz–Mazur style integral model of $X_0(N_0q)$ over the localisation of $\mathbb{Z}$ at $q$: the two cusps as integral sections, the Atkin–Lehner involution $w_q$ pinned on the $j$-finite chart, the degeneracy (forgetful) morphism down to level $N_0$, and the maximal relatively smooth open containing both cusps. It is one of the components used to produce the level-$(N_0,q)$ model package, [`ModularCurve.nonempty_dRModelPackageLevel`](thm.html#ModularCurve.nonempty_dRModelPackageLevel), on which the level-lowering step relies.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_exists_cusps_involution_forgetful_smoothLocus.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicGeometry
open AlgebraicCurve
open ModularCurve ModularCurve.DRLevel
open ModularCurve.IgusaScheme

theorem ModularCurve.DRLevel.exists_cusps_involution_forgetful_smoothLocus
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) :
    ∃ (εinf εzero : SchemeHomOver (𝟙 (Spec (CommRingCat.of (DRLevel.R q)))) (DRLevel.toBase N₀ q))
      (rhoInf : ↥(IgusaScheme.chartAlgInf (N₀ * q) q) →ₐ[DRLevel.R q] DRLevel.R q)
      (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q)
      (theta : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ≃ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
      (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
      (iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
      (iotaInf : ↥(IgusaScheme.chartAlgInf N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q))
      (U : (DRLevel.X N₀ q).Opens) (_ : SmoothOfRelativeDimension 1 (U.ι ≫ DRLevel.toBase N₀ q)),

      (∀ b : ↥(IgusaScheme.chartAlgInf (N₀ * q) q),
        ((rhoInf b : DRLevel.R q) : ℚ) = ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ).coeff 0) ∧
      εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ IgusaScheme.ιInf (N₀ * q) q ∧

      w.hom ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q ∧ w.hom ≫ w.hom = 𝟙 _ ∧ εinf.1 ≫ w.hom = εzero.1 ∧
      (∀ b, ((theta b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) =
        atkinLehnerInvolutionFull N₀ q (b : ↥(modularFunctionFieldFull (N₀ * q)))) ∧
      IgusaScheme.ιFin (N₀ * q) q ≫ w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q ∧

      (∀ b, (((iota0 b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ)) ∧
      IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ IgusaScheme.ιFin N₀ q ∧

      (∀ b, (((iotaInf b : ↥(IgusaScheme.chartAlgInf (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ)) ∧
      IgusaScheme.ιInf (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫ IgusaScheme.ιInf N₀ q ∧

      (∀ V : (DRLevel.X N₀ q).Opens, Smooth (V.ι ≫ DRLevel.toBase N₀ q) → V ≤ U) ∧
      Set.range εinf.1.base ⊆ (U : Set (DRLevel.X N₀ q)) ∧ Set.range εzero.1.base ⊆ (U : Set (DRLevel.X N₀ q)) := by sorry
