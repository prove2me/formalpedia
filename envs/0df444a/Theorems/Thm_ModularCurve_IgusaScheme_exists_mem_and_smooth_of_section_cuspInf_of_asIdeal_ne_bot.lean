-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_mem_and_smooth_of_section_cuspInf_of_asIdeal_ne_bot
-- name    : ModularCurve.IgusaScheme.exists_mem_and_smooth_of_section_cuspInf_of_asIdeal_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/fa4a89a4-cb68-5527-b977-5d604b0468cd
-- title:
--   Smoothness of Igusa's model at the cusp ∞ modulo p
-- statement:
--   Fix an integer $M \geq 1$ and a prime $p$, and write $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$, i.e. $\mathbb{Z}_{(p)}$. Let $F =$ `modularFunctionFieldFull M` be the subfield of $\mathbb{Q}$-Laurent series generated over $\mathbb{Q}$ by the $q$-expansions $\mathrm{qExpand}\,\mathbb{Q}\,d\,j$ for the divisors $d$ of $M$, and let `chartAlgInf M p` be the $R$-subalgebra of $F$ of elements integral over $R[1/j]$, the pole chart of the two-chart scheme [`ModularCurve.IgusaScheme M p`](def/ModularCurve_IgusaScheme.html#L255), which is the pushout of `fFin M p` and `fInf M p`, equipped with the structure morphism `igusaTo M p` to $\operatorname{Spec} R$ obtained from the two inclusions of $R$. The data are: a section $\varepsilon_\infty$ of `igusaTo M p`, that is a morphism $\operatorname{Spec} R \to$ `IgusaScheme M p` whose composite with `igusaTo M p` is the identity; an $R$-algebra homomorphism $\rho_\infty \colon$ `chartAlgInf M p` $\to R$ which on every element $b$ returns, as a rational number, the coefficient of $q^0$ of the Laurent series underlying $b$; the hypothesis that the underlying morphism of $\varepsilon_\infty$ factors as $\operatorname{Spec}$ of $\rho_\infty$ followed by the morphism `IgusaScheme.ιInf M p` of the pole chart into the pushout; and a point $t$ of $\operatorname{Spec} R$ whose prime ideal is nonzero, hence the closed point $(p)$. The conclusion is that there is an open subscheme $W$ of `IgusaScheme M p` containing the image of $t$ under $\varepsilon_\infty$ such that the composite of the open immersion $W \hookrightarrow$ `IgusaScheme M p` with `igusaTo M p` is smooth.
--
--   This is the statement that the reduction modulo $p$ of the cusp $\infty$, given on the pole chart by the constant-term-of-the-$q$-expansion retraction, lies in the smooth locus of Igusa's integral model of $X_0(M)$ over $\mathbb{Z}_{(p)}$, for every level $M$ and every prime $p$; classically this reflects the fact that near $\infty$ the curve is the Tate curve over $\mathbb{Z}_{(p)}[\![q]\!]$. The existence of the explicit open neighbourhood $W$ is what is used in [`ModularCurve.IgusaScheme.exists_smoothLocus_maximal_and_section_mem`](thm.html#ModularCurve.IgusaScheme.exists_smoothLocus_maximal_and_section_mem) to place the cuspidal section inside the smooth locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_mem_and_smooth_of_section_cuspInf_of_asIdeal_ne_bot.lean

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

theorem ModularCurve.IgusaScheme.exists_mem_and_smooth_of_section_cuspInf_of_asIdeal_ne_bot
    (M p : ℕ) [NeZero M] [Fact p.Prime]
    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) (igusaTo M p))
    (rhoInf : ↥(IgusaScheme.chartAlgInf M p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p))
    (hrho : ∀ b : ↥(IgusaScheme.chartAlgInf M p),
      ((rhoInf b : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) = ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ).coeff 0)
    (hεchart : εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ IgusaScheme.ιInf M p)
    (t : ↥(Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) (ht : t.asIdeal ≠ ⊥) :
    ∃ W : (ModularCurve.IgusaScheme M p).Opens, εinf.1.base t ∈ W ∧ Smooth (W.ι ≫ igusaTo M p) := by sorry
