-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_smoothLocus_maximal_and_section_mem
-- name    : ModularCurve.IgusaScheme.exists_smoothLocus_maximal_and_section_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/484121ab-c2aa-5df1-8f9f-8693f082a154
-- title:
--   Maximal smooth locus of the Igusa model contains the cusps
-- statement:
--   Let $M\ge 1$ and let $p$ be a prime, and write $R=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbf{Q}$ consisting of the rationals whose denominator is coprime to $p$ (so $R=\mathbf{Z}_{(p)}$). Let $\mathfrak X=$ [`ModularCurve.IgusaScheme M p`](def/ModularCurve_IgusaScheme.html#L255) be the pushout of the two chart morphisms `fFin`, `fInf`, with structure morphism $c=$ `igusaTo M p` $\colon \mathfrak X\to\operatorname{Spec} R$ obtained by descent from the $R$-algebra structures of the two chart algebras. The data are: a section $\varepsilon_\infty$ of $c$, i.e. a morphism $\operatorname{Spec} R\to\mathfrak X$ whose composite with $c$ is the identity; an $R$-algebra homomorphism $\rho_\infty$ from `chartAlgInf M p`, the algebra of elements of the field `modularFunctionFieldFull M` (generated over $\mathbf{Q}$ inside $\mathbf{Q}((q))$ by the expansions $j(q^d)$ for $d\mid M$) that are integral over $R[j^{-1}]$, to $R$, satisfying the hypothesis that $\rho_\infty(b)$ is the constant Laurent coefficient of $b$ for every $b$; the hypothesis that $\varepsilon_\infty$ is `Spec.map` of $\rho_\infty$ followed by the chart morphism `IgusaScheme.ιInf M p`; and an isomorphism $w\colon\mathfrak X\cong\mathfrak X$ with $w$ followed by $c$ equal to $c$. The conclusion asserts the existence of an open subscheme $U\subseteq\mathfrak X$ such that the restriction $U\hookrightarrow\mathfrak X\to\operatorname{Spec} R$ is smooth of relative dimension $1$, such that every open $V$ with $V\to\operatorname{Spec} R$ smooth satisfies $V\le U$, and such that both the set-theoretic image of $\varepsilon_\infty$ and the image of $\varepsilon_\infty$ followed by $w$ are contained in $U$.
--
--   This is the statement that Igusa's two-chart model of $X_0(M)$ over $\mathbf{Z}_{(p)}$ has a largest open subscheme smooth over the base, that this locus has relative dimension one, and that it contains the cusp $\infty$ (given on the pole chart by the constant-term retraction of $q$-expansions) together with its image under any automorphism of the model over $\mathbf{Z}_{(p)}$, such as the Atkin–Lehner involution. It is used in [`ModularCurve.DRLevel.exists_cusps_involution_forgetful_smoothLocus`](thm.html#ModularCurve.DRLevel.exists_cusps_involution_forgetful_smoothLocus), where the cusps and the involution must be known to lie in the smooth locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_smoothLocus_maximal_and_section_mem.lean

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

open CategoryTheory CategoryTheory.Limits NeronModelInfra ModularCurve
open AlgebraicGeometry
open ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_smoothLocus_maximal_and_section_mem
    (M p : ℕ) [NeZero M] [Fact p.Prime]

    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) (igusaTo M p))
    (rhoInf : ↥(IgusaScheme.chartAlgInf M p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p))
    (hrho : ∀ b : ↥(IgusaScheme.chartAlgInf M p),
      ((rhoInf b : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) = ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ).coeff 0)
    (hεchart : εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ IgusaScheme.ιInf M p)

    (w : ModularCurve.IgusaScheme M p ≅ ModularCurve.IgusaScheme M p) (hw : w.hom ≫ igusaTo M p = igusaTo M p) :
    ∃ (U : (ModularCurve.IgusaScheme M p).Opens) (_ : SmoothOfRelativeDimension 1 (U.ι ≫ igusaTo M p)),
      (∀ V : (ModularCurve.IgusaScheme M p).Opens, Smooth (V.ι ≫ igusaTo M p) → V ≤ U) ∧
      Set.range εinf.1.base ⊆ (U : Set (ModularCurve.IgusaScheme M p)) ∧
      Set.range (εinf.1 ≫ w.hom).base ⊆ (U : Set (ModularCurve.IgusaScheme M p)) := by sorry
