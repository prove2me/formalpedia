-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip
-- name    : LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/25b1690d-937b-5c3d-a1aa-741bb8a6623e
-- title:
--   Tate's local functional equation with φ-uniform γ-factor
-- statement:
--   Let $p$ be a height-one prime of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_p$ for the adic completion, $q = \#(\mathcal O/p)$ for its absolute norm, $\varpi$ for the distinguished uniformiser unit [`NumberField.AdelicLevel.uniformizerUnit`](def/NumberField_AdelicLevel.html#L788), $\psi =$ `psiLocal` (the standard adelic additive character restricted to the place $p$ via the single-place embedding) and $dx$ for `selfDualHaarAt`, the additive Haar measure giving the valuation ring mass $q^{-\ell/2}$, where $\ell$ is the level of $\psi$. Let $\mu : F^\times \to \mathbb C^\times$ be a group homomorphism which is locally constant. Then there exist nonzero polynomials $\Gamma_n, \Gamma_d \in \mathbb C[X]$ and an integer $e_\Gamma$, independent of the test function and of $s$, such that for every $\varphi : F \to \mathbb C$ that is locally constant with compact support, and every $s \in \mathbb C$ with $-1 - \log_q\lVert\mu(\varpi)\rVert < \operatorname{Re} s < -\log_q\lVert\mu(\varpi)\rVert$, one has $$\Big(\int_{F^\times} \hat\varphi(a)\,\mu(a)^{-1}\,|a|^{1+s}\,d^\times a\Big)\,\Gamma_d(q^{-s}) = \Gamma_n(q^{-s})\, q^{e_\Gamma s}\,\Big(\int_{F^\times} \varphi(a)\,\mu(a)\,|a|^{-s}\,d^\times a\Big),$$ where $\hat\varphi(y) = \int_F \varphi(x)\psi(xy)\,dx$ is `tateFourier`, $|a| =$ `modulus` $a$ (the module of multiplication by $a$, equal to $\lVert a\rVert$), and $d^\times a$ is the pull-back along $F^\times \hookrightarrow F$ of $|x|^{-1}\,dx$ restricted to $F \setminus \{0\}$.
--
--   This is Tate's local functional equation at a finite place of $\mathbb Q$, in the form $Z(\hat\varphi,\mu^{-1},1+s) = \gamma\, Z(\varphi,\mu,-s)$ with the $\gamma$-factor written as $q^{e_\Gamma s}$ times a ratio of two fixed nonzero polynomials in $q^{-s}$, so that the same rational data serve every Schwartz–Bruhat test function and every $s$ in the indicated strip; the quasi-character $\mu$ is arbitrary locally constant, not assumed unitary. It is used by [`LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_rational_and_clearedFE`](thm.html#LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_rational_and_clearedFE) in the local analysis feeding the Rankin–Selberg and converse-theorem arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip.lean

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

theorem LanglandsTunnell.TateLocal.exists_gamma_forall_localZeta_tateFourier_mul_eq_of_strip
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hμ : IsLocallyConstant μ) :
    letI := localBorel ℚ p
    ∃ (Γn Γd : Polynomial ℂ) (eΓ : ℤ), Γn ≠ 0 ∧ Γd ≠ 0 ∧
      ∀ (φ : p.adicCompletion ℚ → ℂ), IsSchwartzBruhat φ → ∀ s : ℂ,
        -1 - Real.logb (Ideal.absNorm p.asIdeal : ℝ) ‖((μ (NumberField.AdelicLevel.uniformizerUnit ℚ p) : ℂˣ) : ℂ)‖ < s.re →
        s.re < -Real.logb (Ideal.absNorm p.asIdeal : ℝ) ‖((μ (NumberField.AdelicLevel.uniformizerUnit ℚ p) : ℂˣ) : ℂ)‖ →
          (∫ a : (p.adicCompletion ℚ)ˣ,
              tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) φ (a : p.adicCompletion ℚ) *
                ((μ⁻¹ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 + s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) * Γd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            Γn.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((eΓ : ℂ) * s) *
              (∫ a : (p.adicCompletion ℚ)ˣ,
                φ (a : p.adicCompletion ℚ) * ((μ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-s)
                ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by sorry
