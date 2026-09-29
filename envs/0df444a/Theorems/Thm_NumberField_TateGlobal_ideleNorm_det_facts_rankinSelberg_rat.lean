-- Prove2me | Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_facts_rankinSelberg_rat
-- name    : NumberField.TateGlobal.ideleNorm_det_facts_rankinSelberg_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/35bdbc5d-bbf1-5af0-89df-4d8d8bc6a0d6
-- title:
--   Idelic norms of determinants on GL₂(A_ℚ)
-- statement:
--   Fix a family $\varpi = (\varpi_v)_v$ indexed by the finite places $v$ of $\mathbb{Q}$, with $\varpi_v$ in the valuation ring of $\mathbb{Q}_v$, subject to two hypotheses: the valuation of the image of $\varpi_v$ in $\mathbb{Q}_v$ is $\exp(-1)$, and that image is nonzero. Writing $\|x\| = \mathrm{ideleNorm}\,\mathbb{Q}\,(x)$ for the module $\mathrm{distribHaarChar}$ of the adele ring at an idele $x$, the theorem asserts eleven statements at once. First, for every $g \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ one has $\|\det g\| = |\det(\mathrm{ratArchGL2}\,g)| \cdot \|\det(\mathrm{finFactor}\,g)\|$, where $\mathrm{ratArchGL2}\,g \in \mathrm{GL}_2(\mathbb{R})$ is the component of $g$ at the unique infinite place of $\mathbb{Q}$ and $\mathrm{finFactor}\,g$ is the product of the inverse of its archimedean image with $g$, an element of the kernel of $\mathrm{glArch}$. Second, $\|\det(\mathrm{placeEmbed}\,v\,k)\| = 1$ whenever $k \in \mathrm{GL}_2(\mathbb{Q}_v)$ lies in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), i.e. its image under `localEmbed` lies in the finite level-one subgroup at the unit ideal. Third and fourth, the local matrices $\begin{pmatrix}\varpi_v & \beta\\ 0 & 1\end{pmatrix}$ (any $\beta \in \mathbb{Q}_v$) and $\begin{pmatrix}1 & 0\\ 0 & \varpi_v\end{pmatrix}$, embedded at $v$, have determinant of idelic norm $(\mathrm{absNorm}\,v)^{-1}$, while the scalar matrix $\varpi_v \cdot 1$ gives $(\mathrm{absNorm}\,v)^{-2}$. Next, $\|\det \gamma\| = 1$ for $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ mapped diagonally into the adelic group, and $\|\det(z \cdot 1)\| = \|z\|^2$ for a central idelic scalar $z$. Further, $g \mapsto \|\det g\|$ is continuous; a local $m$ with $\det m = 1$ has $\det(\mathrm{placeEmbed}\,v\,m) = 1$; multiplying on either side by $\mathrm{placeEmbed}\,v\,m$ leaves $\mathrm{ratArchGL2}$ unchanged; and every element of the subgroup $\mathrm{finUnipotent}$ of finite adelic unipotents has determinant $1$ in $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$.
--
--   These are the idelic-norm computations underlying the product formula for $\|\det\|$ on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, together with the values of $\|\det\|$ on the Hecke, torus and central representatives used in the Rankin–Selberg bookkeeping. They are collected in this form for the transport of the unitary twist by a power of $\|\det\|$, cited by [`AutomorphicForm.unitaryTwist_transport_shapedRawVector_transl_rat`](thm.html#AutomorphicForm.unitaryTwist_transport_shapedRawVector_transl_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_ideleNorm_det_facts_rankinSelberg_rat.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem NumberField.TateGlobal.ideleNorm_det_facts_rankinSelberg_rat
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0) :
    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) =
      |((Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝˣ) : ℝ)| *
        TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ))) ∧
    (∀ (v : HeightOneSpectrum (𝓞 ℚ)) (k : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ v k)) = 1) ∧
    (∀ (v : HeightOneSpectrum (𝓞 ℚ)) (β : v.adicCompletion ℚ),
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ v (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v) β))) =
        (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ),
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ v (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
        (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ),
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ v (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
        ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹) ^ 2) ∧
    (∀ γ : GL (Fin 2) ℚ, TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 ℚ) ℚ γ)) = 1) ∧
    (∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 ℚ) ℚ z)) = TateGlobal.ideleNorm ℚ z ^ 2) ∧
    Continuous (fun g : AdelicGL2 (𝓞 ℚ) ℚ => TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)) ∧
    (∀ (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)),
      Matrix.GeneralLinearGroup.det m = 1 → Matrix.GeneralLinearGroup.det (placeEmbed ℚ v m) = 1) ∧
    (∀ (v : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      ratArchGL2 (placeEmbed ℚ v m * g) = ratArchGL2 g ∧ ratArchGL2 (g * placeEmbed ℚ v m) = ratArchGL2 g) ∧
    (∀ (n : RSCarrier.finUnipotent),
      Matrix.GeneralLinearGroup.det (((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) = 1) := by sorry
