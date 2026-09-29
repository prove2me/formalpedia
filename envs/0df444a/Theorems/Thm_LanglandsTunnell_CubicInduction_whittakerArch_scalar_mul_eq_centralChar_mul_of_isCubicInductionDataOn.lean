-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_whittakerArch_scalar_mul_eq_centralChar_mul_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.whittakerArch_scalar_mul_eq_centralChar_mul_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/55841214-82c2-564f-b531-7268aecf174d
-- title:
--   Central character law for the archimedean Whittaker function
-- statement:
--   Let $K$ be a number field whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, let $\psi$ be an additive character of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, let $\mu$ be a homomorphism from the ideles of $K$ to $\mathbb{C}^{\times}$, let `pins` be a choice of carrier data for $\mathbb{Q}$ (a measurable space and measure on adelic $GL_2$, a subset $D$, a subgroup $Z$ of the ideles, level subgroups $U$ indexed by ideals, local generators, and a measurable space and measure on the adeles), and let $S$ be a finite set of finite places of $\mathbb{Q}$. Let $X$ consist of a function `form` on adelic $GL_3$ over $\mathbb{Q}$, a global Whittaker function `whittaker`, local Whittaker functions `whittakerLoc` at each finite place, an archimedean Whittaker function `whittakerArch` on $GL_3$ of the infinite adeles, a character `centralChar` of the ideles, and a dual Whittaker function, and assume `IsCubicInductionDataOn` holds for $K$, `pins`, $\psi$, $\mu$, $S$ and $X$: its hypotheses (left-invariance of `form` under the rational points, the central transformation law via `centralChar`, that `centralChar` is trivial on principal ideles, cuspidality along the two parabolics relative to `pins`, identification of `whittaker` with the $\psi$-Whittaker coefficient of `form`, the $\psi$-Whittaker transformation laws global, local and archimedean, the mirabolic Fourier expansion, factorisation of `whittaker` into the archimedean factor times the local factors at any finite set containing $S$, induced sphericity and level invariance of `whittakerLoc` outside $S$, local multiplicity one, moderate growth, $K$-finiteness of `whittakerArch`, moment and half-plane conditions, and the corresponding conditions for the dual form) are summarised here. Assume in addition that $X.\mathrm{whittakerLoc}_v(1)=1$ for every $v\in S$, and let $E$ be a homomorphism from the units of the infinite adele ring of $\mathbb{Q}$ to the ideles such that for every $u$ the infinite component of $E(u)$ is $u$ and its finite-adelic component is $1$. Then for every unit $z$ of the infinite adele ring and every $g \in GL_3$ of the infinite adele ring, $X.\mathrm{whittakerArch}(z\cdot g) = X.\mathrm{centralChar}(E z)\, X.\mathrm{whittakerArch}(g)$, where $z$ acts through the scalar matrix it defines.
--
--   This records that the archimedean factor of a factorisable $GL_3$ Whittaker function inherits the central transformation law of the global form, with the global central character evaluated at the idele having infinite part $z$ and trivial finite part. It is used in the analysis of the local zeta integrals at $3\times 1$ and in the functional-equation arguments for cubic induction data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_whittakerArch_scalar_mul_eq_centralChar_mul_of_isCubicInductionDataOn.lean

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
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open LanglandsTunnell.CubicLambda LanglandsTunnell.TateLocal UnramifiedWhittaker
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.CubicInduction.whittakerArch_scalar_mul_eq_centralChar_mul_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (pins : CarrierPins ℚ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ (S : Set (HeightOneSpectrum (𝓞 ℚ))) X)
    (h1 : ∀ v ∈ S, X.whittakerLoc v 1 = 1)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    X.whittakerArch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) =
      ((X.centralChar (E z) : ℂˣ) : ℂ) * X.whittakerArch g := by sorry
