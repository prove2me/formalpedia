-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_iso_involutive_iotaFin_comp_eq_atkinLehner_of_not_dvd
-- name    : ModularCurve.IgusaScheme.exists_iso_involutive_iotaFin_comp_eq_atkinLehner_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/aec29a51-451f-5b2a-b34c-fbc2a4aec2a5
-- title:
--   Atkin–Lehner involution wₚ on Igusa's model of X₀(Np)
-- statement:
--   Let $N\ge 1$, let $p$ be a prime with $p \nmid N$, and write $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb{Q}$ consisting of rationals whose denominator is coprime to $p$, and $F =$ `modularFunctionFieldFull (N*p)` for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the expansions $j(q^d)$ for the nonzero divisors $d$ of $Np$. Let $\mathfrak{X} =$ [`ModularCurve.IgusaScheme (N*p) p`](def/ModularCurve_IgusaScheme.html#L255) be the two-chart model obtained as the pushout of the two chart inclusions, with finite chart $\operatorname{Spec}$ of `chartAlgFin (N*p) p`, the $R$-subalgebra of elements of $F$ integral over $R[j]$, structure morphism `igusaTo` to $\operatorname{Spec} R$ and chart morphism `ιFin`. The assertion is that there exist an isomorphism $w : \mathfrak{X} \cong \mathfrak{X}$ and an $R$-algebra automorphism $\theta$ of `chartAlgFin (N*p) p` such that: $w$ followed by `igusaTo` equals `igusaTo`; $w.hom$ composed with itself is the identity; for every $b$ in the finite chart algebra, $\theta(b)$ and $w_p(b)$ agree in $F$, where $w_p =$ `atkinLehnerInvolutionFull N p` is the chosen $\mathbb{Q}$-algebra automorphism of $F$ interchanging $j(q^d)$ and $j(q^{dp})$ for all nonzero $d \mid N$ (such an automorphism exists under the stated hypotheses); and `ιFin` followed by $w.hom$ equals $\operatorname{Spec}\theta$ followed by `ιFin`, i.e. $w$ restricts on the finite chart to $\operatorname{Spec}\theta$.
--
--   This realises the partial Atkin–Lehner involution $w_p$ of the function field of $X_0(Np)$ as an involutive automorphism of Igusa's integral two-chart model over $\mathbb{Z}_{(p)}$, pinned down on the $j$-finite chart by an explicit ring automorphism; note that the statement provides no compatibility on the pole chart, since $w_p$ does not preserve the integral closure of $R[1/j]$. It is used in the analysis of the cusps and the smooth locus of the level structure, via [`ModularCurve.DRLevel.exists_cusps_involution_forgetful_smoothLocus`](thm.html#ModularCurve.DRLevel.exists_cusps_involution_forgetful_smoothLocus).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_iso_involutive_iotaFin_comp_eq_atkinLehner_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ModularCurve
open ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_iso_involutive_iotaFin_comp_eq_atkinLehner_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    ∃ (w : ModularCurve.IgusaScheme (N * p) p ≅ ModularCurve.IgusaScheme (N * p) p)
      (theta : ↥(IgusaScheme.chartAlgFin (N * p) p) ≃ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(IgusaScheme.chartAlgFin (N * p) p)),
      w.hom ≫ igusaTo (N * p) p = igusaTo (N * p) p ∧
      w.hom ≫ w.hom = 𝟙 _ ∧
      (∀ b, ((theta b : ↥(IgusaScheme.chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
        atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p)))) ∧
      IgusaScheme.ιFin (N * p) p ≫ w.hom =
        Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N * p) p := by sorry
