-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_iso_pullback_igusaTo_rat_twoChartIntegralModel_and_iotaFin
-- name    : ModularCurve.IgusaScheme.exists_iso_pullback_igusaTo_rat_twoChartIntegralModel_and_iotaFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/e679a9b7-ffd9-5c28-943c-e5e7e8b8038b
-- title:
--   Generic fibre of the Igusa scheme as rational two-chart model
-- statement:
--   Let $N \ge 1$ and let $q$ be a prime. Write $\mathbb{Z}_{(q)}$ for the subring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $q$, and $F$ for `modularFunctionFieldFull N`, the subfield of $\mathbb{Q}((T))$-type Laurent series generated over $\mathbb{Q}$ by the divisor expansions attached to $N$, with distinguished element $j =$ `jFull N`. The Igusa scheme `IgusaScheme N q` is the pushout gluing $\operatorname{Spec}$ of `IgusaScheme.chartAlgFin N q` (the elements of $F$ integral over $\mathbb{Z}_{(q)}[j]$) to $\operatorname{Spec}$ of the corresponding algebra for $j^{-1}$, with structure morphism `igusaTo N q` to $\operatorname{Spec} \mathbb{Z}_{(q)}$ and finite-chart morphism `ιFin N q`; `TwoChartIntegralModel ℚ F j` is the analogous pushout over $\mathbb{Q}$, with structure morphism `TwoChartIntegralModel.toBase` and finite-chart morphism `TwoChartIntegralModel.ιFin`. The assertion is the existence of: an isomorphism $\varepsilon$ from the fibre product of `igusaTo N q` with $\operatorname{Spec}$ of the inclusion $\mathbb{Z}_{(q)} \to \mathbb{Q}$ onto `TwoChartIntegralModel ℚ F j`; an isomorphism $\kappa$ from the fibre product of `ιFin N q` with the first projection of that pullback onto $\operatorname{Spec}$ of `TwoChartIntegralModel.chartAlgFin ℚ F j`; and a $\mathbb{Z}_{(q)}$-algebra map $\theta$ from `IgusaScheme.chartAlgFin N q` to `TwoChartIntegralModel.chartAlgFin ℚ F j`, such that $\varepsilon$ followed by `toBase` is the second projection to $\operatorname{Spec}\mathbb{Q}$ (so $\varepsilon$ is an isomorphism over $\mathbb{Q}$); the second projection of the chart pullback followed by $\varepsilon$ equals $\kappa$ followed by the finite-chart morphism of the $\mathbb{Q}$-model; $\theta$ is the identity on underlying elements of $F$; and $\kappa$ followed by $\operatorname{Spec}\theta$ is the first projection of the chart pullback.
--
--   This identifies the generic fibre of the Igusa integral model of the modular curve of level $N$ over $\mathbb{Z}_{(q)}$ with the two-chart integral model of the modular function field $F$ over $\mathbb{Q}$, matching finite chart with finite chart and recording the chart-ring inclusion that induces the identification. It is used in the study of the base change of the Igusa scheme to $\mathbb{Q}$, in particular in establishing finiteness and surjectivity properties of that change of base and the resulting description of function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_iso_pullback_igusaTo_rat_twoChartIntegralModel_and_iotaFin.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme AlgebraicCurve

theorem ModularCurve.IgusaScheme.exists_iso_pullback_igusaTo_rat_twoChartIntegralModel_and_iotaFin
    (N q : ℕ) [NeZero N] [Fact q.Prime] :
    ∃ (ε : pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ))) ≅
        TwoChartIntegralModel ℚ ↥(modularFunctionFieldFull N) (jFull N))
      (κ : pullback (ιFin N q)
          (pullback.fst (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)))) ≅
        Spec (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℚ ↥(modularFunctionFieldFull N) (jFull N))))
      (θ : ↥(IgusaScheme.chartAlgFin N q) →ₐ[↥(GaloisRep.ratLocalizedAt q)]
        ↥(TwoChartIntegralModel.chartAlgFin ℚ ↥(modularFunctionFieldFull N) (jFull N))),

      ε.hom ≫ TwoChartIntegralModel.toBase ℚ ↥(modularFunctionFieldFull N) (jFull N) = pullback.snd _ _ ∧

      pullback.snd (ιFin N q)
          (pullback.fst (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)))) ≫ ε.hom =
        κ.hom ≫ TwoChartIntegralModel.ιFin ℚ ↥(modularFunctionFieldFull N) (jFull N) ∧

      (∀ x, (θ x : ↥(modularFunctionFieldFull N)) = x) ∧
      κ.hom ≫ Spec.map (CommRingCat.ofHom θ.toRingHom) =
        pullback.fst (ιFin N q)
          (pullback.fst (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)))) := by sorry
