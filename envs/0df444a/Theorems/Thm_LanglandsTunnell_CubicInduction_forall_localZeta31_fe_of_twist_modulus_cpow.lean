-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_forall_localZeta31_fe_of_twist_modulus_cpow
-- name    : LanglandsTunnell.CubicInduction.forall_localZeta31_fe_of_twist_modulus_cpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/c74589b7-f3fe-512b-a83e-bd44b4180513
-- title:
--   Unramified twist shifts the local (3,1) functional equation
-- statement:
--   Fix a height-one prime $p$ of $\mathcal O_{\mathbb Q}$, write $N=\operatorname{absNorm}(p)$, and let $\mu$ denote the measure on $(\mathbb Q_p)^\times$ obtained by pulling back along the inclusion of units the multiplicative modification $dx/\lVert x\rVert$ of the self-dual additive Haar measure $\nu=$ `selfDualHaarAt ℚ p`. Let $W_3$ be a complex-valued function on $\mathrm{GL}_3(\mathbb Q_p)$, let $\eta,\chi\colon(\mathbb Q_p)^\times\to\mathbb C^\times$ be multiplicative characters, let $t\in\mathbb C$ and assume $\chi(a)=\eta(a)\,\mathrm{modulus}(a)^{t}$ for all units $a$, where $\mathrm{modulus}$ is the module of multiplication. Let $C\in\mathbb C$ and $k\in\mathbb Z$. The hypothesis is that for every $g\in\mathrm{GL}_3(\mathbb Q_p)$ there are $Q_1,Q_2\in\mathbb C[X]$ with $Q_2\neq0$, an $n\in\mathbb Z$ and abscissae $\sigma_0,\sigma_1\in\mathbb R$ such that: for $\operatorname{Re}s>\sigma_0$ the function $a\mapsto W_3(\iota(\mathrm{diag}(a,1))g)\,\eta(a)\,\mathrm{modulus}(a)^{s-1}$ is $\mu$-integrable and $\mathrm{localZeta30}(s,g)\cdot Q_2(N^{-s})=Q_1(N^{-s})\,N^{ns}$; for $\operatorname{Re}s>\sigma_1$ the function $(a,x)\mapsto W_3(\mathrm{longWeyl}_3\,{}^{t}(\iota(\mathrm{diag}(a,1))\,u_{21}(x)\,w'\,{}^{t}g^{-1})^{-1})\,\eta(a)^{-1}\mathrm{modulus}(a)^{s-1}$ is $\mu\otimes\nu$-integrable; and for $\operatorname{Re}(1-s)>\sigma_1$ the dual integral satisfies $\mathrm{localZetaDual31}(1-s,g)\cdot Q_2(N^{-s})=Q_1(N^{-s})\,N^{ns}\,(C\,N^{ks})$. The conclusion is the same statement with $\eta$ replaced by $\chi$ throughout (again with existentially quantified $Q_1,Q_2,n,\sigma_0,\sigma_1$) and with the constant $C\,N^{ks}$ replaced by $C\,N^{kt}\,N^{ks}$; the integer $k$ and the number $C$ are unchanged.
--
--   This records the effect of an unramified twist $\chi=\eta\,\lVert\cdot\rVert^{t}$ on the Jacquet–Piatetski-Shapiro–Shalika local zeta integrals attached to a Whittaker function on $\mathrm{GL}_3(\mathbb Q_p)$: the twist shifts the spectral variable by $t$, rescales the rational data in $N^{-s}$, and multiplies the monomial constant of the functional equation by $N^{kt}$. It is used to transport functional equations established for unitary characters to the (possibly non-unitary) inducing quasi-characters occurring in the principal-series partner, and is cited by the constructions of primal and dual middle data for the Rankin–Selberg local integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_forall_localZeta31_fe_of_twist_modulus_cpow.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.CubicInduction.forall_localZeta31_fe_of_twist_modulus_cpow
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W₃base : LocalGL3 p → ℂ)
    (η χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (t : ℂ)
    (hχ : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χ a : ℂˣ) : ℂ) = ((η a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ t))
    (C : ℂ) (k : ℤ)
    (h31 :
              ∀ g : LocalGL3 p,
                letI := localBorel ℚ p
                ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                  IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
                    W₃base η g σ₀ ∧
                  (∀ s : ℂ, σ₀ < s.re →
                    localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base η s g *
                      Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                  IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) (η)⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
                  (∀ s : ℂ, σ₁ < (1 - s).re →
                    localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
                      W₃base η (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                      (C * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)))) :
    ∀ g : LocalGL3 p,
                letI := localBorel ℚ p
                ∃ (Q₁ Q₂ : Polynomial ℂ) (n : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
                  IsLocalZeta30ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
                    W₃base χ g σ₀ ∧
                  (∀ s : ℂ, σ₀ < s.re →
                    localZeta30 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) W₃base χ s g *
                      Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s)) ∧
                  IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p) (dualWhittakerFn3 W₃base) (χ)⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
                  (∀ s : ℂ, σ₁ < (1 - s).re →
                    localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
                      W₃base χ (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                    Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * s) *
                      (C * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * t) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s))) := by sorry
