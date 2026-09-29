-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_localChar_centralChar_le_inducedLevelAt_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_localChar_centralChar_le_inducedLevelAt_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/8db9c887-7ef2-5719-9c5e-3bf604d4da6f
-- title:
--   Conductor bound for the local central character at unramified v
-- statement:
--   Let $K$ be a number field of degree $3$ over $\mathbb{Q}$, with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, let $\psi$ be an additive character of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, and let $\mu$ be a homomorphism from the ideles of $K$ to $\mathbb{C}^{\times}$ which is an admissible twist, i.e. trivial on the image of $K^{\times}$, continuous, and of absolute value $1$ at every idele. Let `pins` be a choice of carrier data for $\mathbb{Q}$ (a measurable space and measure on the adelic $\mathrm{GL}_2$, a fundamental domain, a central subgroup, level subgroups attached to ideals, local generators, and a measurable space and measure on the adeles), and let $X$ consist of a function `X.form` on the adelic $\mathrm{GL}_3$ of $\mathbb{Q}$, its Whittaker function, local Whittaker functions `X.whittakerLoc v`, an archimedean Whittaker function, a central character `X.centralChar` on the ideles of $\mathbb{Q}$, and a dual Whittaker function. Assume `IsCubicInductionDataOn K pins ψ μ S X`, where $S$ is the set of finite places $v$ of $\mathbb{Q}$ that are bad for $\mu$ (ramified in $K$, or twist-ramified above $v$); this is the conjunction of the automorphy of `X.form` under the rational points, its transformation by `X.centralChar` under the centre, the idele-class property of `X.centralChar`, cuspidality along the two parabolics attached to `pins`, the identification of `X.whittaker` with the $\psi$-Whittaker integral of `X.form` and the $\psi$-Whittaker transformation law, the mirabolic Fourier expansion recovering `X.form`, the local Whittaker laws, factorisation of `X.whittaker` into the archimedean factor and finitely many local factors over any finite set containing $S$, inducedness-sphericity of `X.whittakerLoc v` outside $S$, invariance of `X.whittakerLoc v` under the congruence subgroup of level `inducedLevelAt K μ v` at places outside $S$ unramified in $K$, local multiplicity one, moderate growth, $K$-finiteness of the archimedean factor, the moment and half-plane conditions, and the corresponding statements for the dual form and dual Whittaker function. Assume further that `X.form` is continuous and non-zero, and let $v$ be a finite place of $\mathbb{Q}$ unramified in $K$, in the sense that no prime of $\mathcal{O}_K$ in the fibre over $v$ has ramification index different from $1$. Then there is a natural number $a$ with $a \le \mathrm{inducedLevelAt}\,K\,\mu\,v = \sum_{\mathfrak{P} \mid v} f(\mathfrak{P}\mid v)\,a(\mu_{\mathfrak{P}})$, the sum over the fibre of the residue degrees times the conductor exponents of the local components of $\mu$, such that the local component at $v$ of `X.centralChar`, obtained by restricting it along the inclusion of the units of the $v$-adic completion of $\mathbb{Q}$ into the ideles, has conductor exponent exactly $a$: it is trivial on the $a$-th higher unit group at $v$, and for every $m < a$ there is a unit in the $m$-th higher unit group on which it is non-trivial.
--
--   This is the conductor bound for the central character of cubic induction data at a place unramified in the cubic field: the local central character is, up to an unramified quadratic factor, the product of the restrictions of the local components of $\mu$, whence its conductor exponent is bounded by the induced level at $v$. It feeds the local zeta and functional-equation computations at the bad and deep places in the converse-theorem input for the Langlands–Tunnell construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_localChar_centralChar_le_inducedLevelAt_of_isCubicInductionDataOn.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg MeasureTheory
open LanglandsTunnell.CubicInduction
open LanglandsTunnell.CubicLambda LanglandsTunnell.TateLocal UnramifiedWhittaker
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_localChar_centralChar_le_inducedLevelAt_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (pins : CarrierPins ℚ) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hF : X.form ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hKv : ¬ IsRamifiedIn K v) :
    ∃ a ≤ inducedLevelAt K μ v,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (NumberField.TateGlobal.localChar X.centralChar v) a := by sorry
