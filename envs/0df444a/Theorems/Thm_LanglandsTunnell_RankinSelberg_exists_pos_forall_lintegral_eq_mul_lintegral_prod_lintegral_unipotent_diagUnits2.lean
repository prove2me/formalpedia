-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_eq_mul_lintegral_prod_lintegral_unipotent_diagUnits2
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_forall_lintegral_eq_mul_lintegral_prod_lintegral_unipotent_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/7d7d169c-bf8a-5c98-8c31-6d00126de943
-- title:
--   Iwasawa integration formula for Haar measure on GL₂(ℚₚ)
-- statement:
--   Let $p$ be a height-one prime of $\mathcal{O}_{\mathbb Q}$, i.e. a finite place of $\mathbb Q$, and equip $\mathrm{GL}_2(\mathbb{Q}_p)$ and $\mathbb{Q}_p$ with their Borel $\sigma$-algebras (`localGLBorel` and `localBorel`, the Borel structures of the topologies, together with the corresponding `BorelSpace` instance). The assertion is that for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ there is a real $\kappa>0$ such that for every measurable $G:\mathrm{GL}_2(\mathbb{Q}_p)\to[0,\infty]$ one has $$\int G\,d\mu_2=\kappa\int\Bigl(\int_{\mathbb{Q}_p}G\bigl(n(x)\,d(a_1,a_2)\,k\bigr)\,dx\Bigr)\,\bigl\lVert a_2a_1^{-1}\bigr\rVert\,d\nu(k,a_1,a_2),$$ all integrals being lower Lebesgue integrals in $[0,\infty]$. Here $n(x)$ is `unipotent x`, the matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $d(a_1,a_2)$ is `diagUnits2 a₁ a₂`, the diagonal matrix with entries $a_1,a_2\in\mathbb{Q}_p^\times$; $dx$ is `selfDualHaarAt ℚ p`, the additive Haar measure giving $\mathcal{O}_p$ mass $(\mathrm{absNorm}\,p)^{-\mathrm{addCharLevel}(\psi_p)/2}$; $\lVert\cdot\rVert$ is `modulus`, the module of $\mathbb{Q}_p$ evaluated at $a_2a_1^{-1}$; and $\nu$ is the product of $\mu_2$ restricted to [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along `localEmbed` of the finite-adelic level-one subgroup at the unit ideal, with two copies of the multiplicative measure $\lVert a\rVert^{-1}\,da$ on $\mathbb{Q}_p^\times$, obtained as `Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))`.
--
--   This is the Iwasawa integration formula at a finite place: Haar measure on $\mathrm{GL}_2(\mathbb{Q}_p)$ is decomposed, up to a positive constant, along the coordinates $g=n(x)\,\mathrm{diag}(a_1,a_2)\,k$ with $k$ in the level-one compact subgroup, the extra factor $\lVert a_2/a_1\rVert$ being the modulus of the Borel subgroup. It serves as the measure-theoretic input for the local Rankin–Selberg and Whittaker computations, and is used in establishing integrability of Jacquet integrals and of Whittaker functions against principal series at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_eq_mul_lintegral_prod_lintegral_unipotent_diagUnits2.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.RankinSelberg
open MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_lintegral_eq_mul_lintegral_prod_lintegral_unipotent_diagUnits2
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∃ κ : ℝ, 0 < κ ∧
        ∀ G : GL (Fin 2) (p.adicCompletion ℚ) → ENNReal, Measurable G →
          ∫⁻ g, G g ∂μ₂ =
            ENNReal.ofReal κ *
              ∫⁻ q : GL (Fin 2) (p.adicCompletion ℚ) × ((p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ),
                (∫⁻ x : p.adicCompletion ℚ, G (unipotent x * diagUnits2 q.2.1 q.2.2 * q.1) ∂(selfDualHaarAt ℚ p)) *
                  (modulus ((q.2.2 * q.2.1⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ENNReal)
                ∂((μ₂.restrict (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ)))).prod
                  ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod
                    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))) := by sorry
