-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_rational_localZeta_of_isSchwartzBruhat_of_logb_lt_re
-- name    : LanglandsTunnell.TateLocal.exists_rational_localZeta_of_isSchwartzBruhat_of_logb_lt_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/00bf4436-582f-5035-b680-d6cd32bdeea7
-- title:
--   Convergence and rationality of local Tate zeta integrals over ℚ
-- statement:
--   Let $p$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, write $F_p$ for the $p$-adic completion of $\mathbb{Q}$ and $q=\mathrm{absNorm}(p)$, and equip $F_p$ with its Borel $\sigma$-algebra. Let $\mu\colon F_p^\times\to\mathbb{C}^\times$ be a locally constant group homomorphism and let $\varphi\colon F_p\to\mathbb{C}$ be Schwartz–Bruhat, i.e. locally constant with compact support. The measure used on $F_p^\times$ is the comap along $F_p^\times\hookrightarrow F_p$ of `mulMeasure (selfDualHaarAt ℚ p)`, namely the restriction to $F_p\setminus\{0\}$ of the additive Haar measure scaled so that $\mathcal{O}_p$ has measure $q^{-n/2}$ (with $n$ the level of the standard local additive character, the largest $n$ with $\psi$ trivial on $\{v(x)\le \exp n\}$), multiplied by the density $x\mapsto \mathrm{modulus}(x)^{-1}$, where $\mathrm{modulus}(x)$ is the module of $x$, equal to $\|x\|$. The assertion is the existence of polynomials $P,Q\in\mathbb{C}[X]$ with $Q\neq 0$ and an integer $m$, all independent of $s$, such that for every $s\in\mathbb{C}$ with $\log_q\lvert\mu(\varpi)\rvert<\operatorname{Re} s$, where $\varpi$ is the distinguished uniformiser unit at $p$, the function $a\mapsto \varphi(a)\,\mu(a)\,\mathrm{modulus}(a)^s$ is integrable on $F_p^\times$ and its integral $Z$ satisfies $Z\cdot Q(q^{-s})=q^{ms}\,P(q^{-s})$.
--
--   This is the local theory of Tate zeta integrals at a finite place of $\mathbb{Q}$: absolute convergence on the half-plane $\operatorname{Re} s>\log_q\lvert\mu(\varpi)\rvert$ together with rationality of the zeta integral as a function of $q^{-s}$, in the cleared form $Z\cdot Q(q^{-s})=q^{ms}P(q^{-s})$. It feeds the construction of the local gamma factor and the cleared local functional equation in [`LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_rational_and_clearedFE`](thm.html#LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_rational_and_clearedFE), where the rational expression is evaluated inside Tate's critical strip.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_rational_localZeta_of_isSchwartzBruhat_of_logb_lt_re.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

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

theorem LanglandsTunnell.TateLocal.exists_rational_localZeta_of_isSchwartzBruhat_of_logb_lt_re
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hμ : IsLocallyConstant μ)
    (φ : p.adicCompletion ℚ → ℂ) (hφ : IsSchwartzBruhat φ) :
    letI := localBorel ℚ p
    ∃ (P Q : Polynomial ℂ) (m : ℤ), Q ≠ 0 ∧
      ∀ s : ℂ, Real.logb (Ideal.absNorm p.asIdeal : ℝ) ‖((μ (NumberField.AdelicLevel.uniformizerUnit ℚ p) : ℂˣ) : ℂ)‖ < s.re →
        Integrable (fun a : (p.adicCompletion ℚ)ˣ =>
          φ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s)
          (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        (∫ a : (p.adicCompletion ℚ)ˣ,
            φ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by sorry
