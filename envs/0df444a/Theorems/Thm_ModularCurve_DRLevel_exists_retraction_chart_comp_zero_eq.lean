-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_exists_retraction_chart_comp_zero_eq
-- name    : ModularCurve.DRLevel.exists_retraction_chart_comp_zero_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/9e628506-ea00-583c-89d7-f0590213e5ba
-- title:
--   Chart retraction attached to a section of π mod q
-- statement:
--   Fix $N_0 \neq 0$ and a prime $q$ with $q \nmid N_0$, write $R =$ `DRLevel.R q` for the base ring, and let $\mathcal O_{N_0} =$ `IgusaScheme.chartAlgFin N₀ q` and $\mathcal O =$ `IgusaScheme.chartAlgFin (N₀ * q) q` be the $j$-finite chart algebras, i.e. the $R$-subalgebras of the level-$N_0$, resp. level-$N_0q$, modular function field consisting of the elements integral over $R[j]$. The data are: a morphism $\pi$ from the Igusa model $X(N_0q)$ to $X_0(N_0)$ commuting with the two structure morphisms to $\operatorname{Spec} R$; an $R$-algebra map $\iota_0 : \mathcal O_{N_0} \to \mathcal O$ preserving $q$-expansions (each $\iota_0 b$ has the same image in $\mathrm{LaurentSeries}\ \mathbb{Q}$ as $b$), such that on the $j$-finite charts $\pi$ is read as $\operatorname{Spec} \iota_0$, i.e. `ιFin (N₀*q) q` followed by $\pi$ equals $\operatorname{Spec}\iota_0$ followed by `ιFin N₀ q`; an algebraically closed field $\kappa$ of characteristic $q$ which is an $R$-algebra; chart morphisms $c_0 : \operatorname{Spec}(\kappa \otimes_R \mathcal O_{N_0}) \to$ `fibre0`, and $c : \operatorname{Spec}(\kappa \otimes_R \mathcal O) \to$ `fibre`, into the fibre products defining the special fibres of $X_0(N_0)$ and of $X(N_0q)$ over $\kappa$, each pinned by the requirement that composing with the first projection gives $\operatorname{Spec}$ of the right inclusion followed by the relevant $j$-finite chart immersion and composing with the second projection gives $\operatorname{Spec}$ of the left inclusion $\kappa \to \kappa \otimes_R -$; and a pair `comp` of morphisms from the special fibre of $X_0(N_0)$ to that of $X(N_0q)$, both over $\operatorname{Spec}\kappa$ and both closed immersions, with `comp 0` a section of the base change `fibreMap0 π` of $\pi$ to $\kappa$. The conclusion is the existence of a $\kappa$-algebra homomorphism $\sigma_0 : \kappa \otimes_R \mathcal O \to \kappa \otimes_R \mathcal O_{N_0}$ which is a retraction of $\mathrm{id}_\kappa \otimes \iota_0$, and through which `comp 0` is read on the charts: $c_0$ followed by `comp 0` equals $\operatorname{Spec}\sigma_0$ followed by $c$. Only `comp 0` occurs in the conclusion, the second member of the pair being carried along as part of the packaged data.
--
--   This is the chart-level form of the Deligne–Rapoport and Katz–Mazur description of the component of $X_0(N_0q) \otimes \mathbb{F}_q$ on which the forgetful map to $X_0(N_0)$ is an isomorphism: the section is recognised on the $j$-finite affine charts as the spectrum of an explicit retraction of the base-changed forgetful inclusion. It feeds the downstream analysis of that component, including the statements about minimal primes of the $j$-infinite chart, the identification of nodes, and reducedness of the relevant pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_exists_retraction_chart_comp_zero_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
open scoped TensorProduct

theorem ModularCurve.DRLevel.exists_retraction_chart_comp_zero_eq
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hiota : ∀ b, (((iota0 b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hpichart : IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ IgusaScheme.ιFin N₀ q)

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] [Algebra (DRLevel.R q) κ]

    (c₀ : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) ⟶
      DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom) ≫ IgusaScheme.ιFin N₀ q)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q)))))
    (c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ⟶
      DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q)))))

    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)))
    (hcomp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hcomp_ci : ∀ i, IsClosedImmersion (comp i))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) = 𝟙 _) :
    ∃ σ₀ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[κ]
        κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q),
      (∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z) ∧
      c₀ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c := by sorry
