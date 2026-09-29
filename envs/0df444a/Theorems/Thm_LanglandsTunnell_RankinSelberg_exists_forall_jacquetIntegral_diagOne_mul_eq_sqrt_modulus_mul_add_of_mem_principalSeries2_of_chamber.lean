-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/99add708-b39b-56f2-8fe7-4109a3a6f43e
-- title:
--   Two-exponent asymptotics of chamber Jacquet integrals on small torus
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, and write $F$ for the completion $\mathbb{Q}_p$ at $p$. Let $\mu_0,\mu_1 : F^\times \to \mathbb{C}^\times$ be locally constant characters whose absolute values are given by real exponents $\sigma_0,\sigma_1$, in the sense that $\|\mu_i(a)\| = \|a\|^{\sigma_i}$ for all $a \in F^\times$, and assume $\sigma_1 < \sigma_0$. Let $\varphi : \mathrm{GL}_2(F) \to \mathbb{C}$ belong to `principalSeries2 p μ`, i.e. $\varphi$ is locally constant, invariant under left translation by the upper unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $\varphi(\mathrm{diag}(a_0,a_1)g) = \mu_0(a_0)\mu_1(a_1)\sqrt{\|a_0\|/\|a_1\|}\,\varphi(g)$. Then, for the Borel $\sigma$-algebra on $F$, there exist a real $c > 0$ and functions $C_0, C_1 : \mathrm{GL}_2(F) \to \mathbb{C}$ such that for every $k$ in the subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the preimage at $p$ of the finite-adelic level-one subgroup for the unit ideal) and every $y \in F^\times$ with $\|y\| \le c$, the Jacquet integral $$\int_F \psi_p(x)\,\varphi\!\left(\begin{pmatrix}0&1\\1&0\end{pmatrix}\begin{pmatrix}1&x\\0&1\end{pmatrix}\mathrm{diag}(y,1)\,k\right)dx,$$ taken against the self-dual Haar measure `selfDualHaarAt ℚ p` and the standard local additive character $\psi_p$, equals $\sqrt{\mathrm{modulus}(y)}\bigl(C_1(k)\mu_1(y) + C_0(k)\mu_0(y)\bigr)$, where $\mathrm{modulus}$ is the module of multiplication by $y$ on $F$ (equal to $\|y\|$).
--
--   This is the small-$|y|$ expansion of the Whittaker function obtained as the Jacquet integral of a principal-series vector, in the chamber $\sigma_1 < \sigma_0$ where the integral converges: on the torus elements $\mathrm{diag}(y,1)$ it becomes exactly $|y|^{1/2}$ times a linear combination of the two characters $\mu_0, \mu_1$, with coefficients depending on $k$ but with a threshold $c$ uniform over the maximal compact subgroup at $p$. It feeds the local computations of the Rankin–Selberg and torus zeta integrals used in the converse-theorem input to the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber.lean

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

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.exists_forall_jacquetIntegral_diagOne_mul_eq_sqrt_modulus_mul_add_of_mem_principalSeries2_of_chamber
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∃ (c : ℝ) (C₀ C₁ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ), 0 < c ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ (y : (p.adicCompletion ℚ)ˣ), ‖(y : p.adicCompletion ℚ)‖ ≤ c →
        (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x * φ (antidiagonal2 p * upperUnipotent2 p x * (diagOne y * k)) ∂(selfDualHaarAt ℚ p)) =
          ((Real.sqrt (modulus (y : p.adicCompletion ℚ)) : ℝ) : ℂ) * (C₁ k * ((μ 1 y : ℂˣ) : ℂ) + C₀ k * ((μ 0 y : ℂˣ) : ℂ)) := by sorry
