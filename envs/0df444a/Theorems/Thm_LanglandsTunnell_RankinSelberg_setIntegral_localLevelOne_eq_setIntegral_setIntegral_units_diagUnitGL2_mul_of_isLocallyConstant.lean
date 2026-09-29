-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_setIntegral_localLevelOne_eq_setIntegral_setIntegral_units_diagUnitGL2_mul_of_isLocallyConstant
-- name    : LanglandsTunnell.RankinSelberg.setIntegral_localLevelOne_eq_setIntegral_setIntegral_units_diagUnitGL2_mul_of_isLocallyConstant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/95910543-2a9d-5d20-972f-013fc2cbb6e7
-- title:
--   Unit-torus average over the local level-one subgroup
-- statement:
--   Let $p$ be a nonzero prime ideal of $\mathbb{Z}=\mathcal{O}_{\mathbb{Q}}$, so that $\mathbb{Q}_p :=$ `p.adicCompletion ℚ` carries its Borel $\sigma$-algebra, and likewise $\mathrm{GL}_2(\mathbb{Q}_p)$ (with the corresponding `BorelSpace` instance). Write $\nu$ for the measure on $\mathbb{Q}_p^{\times}$ obtained by pulling back along $u \mapsto u$ the measure `mulMeasure (selfDualHaarAt ℚ p)`, i.e. the restriction of the self-dual additive Haar measure of $\mathbb{Q}_p$ — the additive Haar measure normalised on the valuation ring, scaled by $(\mathrm{absNorm}\, p)^{-\mathrm{addCharLevel}(\psi_p)/2}$ — to the nonzero elements, with density $|x|^{-1}$ given by the inverse of the module `modulus`; let $S = \{u \in \mathbb{Q}_p^{\times} : v(u) = 1\}$ be the units of valuation $1$, and let $K$ be the subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the embedding [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) of $\mathrm{GL}_2(\mathbb{Q}_p)$ into $\mathrm{GL}_2$ of the finite adèles of the level-one subgroup `finiteLevelOne` for the unit ideal. Then for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ and every locally constant $F : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$: $\nu(S) \neq 0$ and $\nu(S) \neq \infty$; $F$ is integrable on $K$ for $\mu_2$; the function $k \mapsto \int_{S} F(\mathrm{diag}(u,1)\,k)\,d\nu(u)$, where $\mathrm{diag}(u,1)$ is `diagUnitGL2 u`, is integrable on $K$ for $\mu_2$; and $$\nu(S)\int_{K} F(k)\,d\mu_2(k) = \int_{K}\Bigl(\int_{S} F(\mathrm{diag}(u,1)\,k)\,d\nu(u)\Bigr)d\mu_2(k),$$ the volume $\nu(S)$ entering as the complex number given by its real value.
--
--   This is the Haar-measure computation that lets an integral over the local level-one subgroup be replaced by its average over left translation by the diagonal unit torus $\mathrm{diag}(u,1)$, $u$ a unit of valuation $1$, together with the finiteness and non-vanishing of the volume of that torus and the integrability needed for the interchange. It is used in the Rankin–Selberg part of the Langlands–Tunnell input, where the averaged integrand isolates a torus shell coefficient and the deep shells are shown to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_setIntegral_localLevelOne_eq_setIntegral_setIntegral_units_diagUnitGL2_mul_of_isLocallyConstant.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.setIntegral_localLevelOne_eq_setIntegral_setIntegral_units_diagUnitGL2_mul_of_isLocallyConstant
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (F : GL (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant F →
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} ≠ 0 ∧
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} ≠ ⊤ ∧
      IntegrableOn F (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))) μ₂ ∧
      IntegrableOn (fun k : GL (Fin 2) (p.adicCompletion ℚ) =>
          ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1}, F (diagUnitGL2 u * k)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
        (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))) μ₂ ∧
      (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1}).toReal : ℂ) *
          ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))), F k ∂μ₂ =
        ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
          (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1}, F (diagUnitGL2 u * k)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∂μ₂ := by sorry
