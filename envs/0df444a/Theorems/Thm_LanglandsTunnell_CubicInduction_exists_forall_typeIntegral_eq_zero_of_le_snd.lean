-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_snd
-- name    : LanglandsTunnell.CubicInduction.exists_forall_typeIntegral_eq_zero_of_le_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/b30fa923-f4ea-55d7-bec8-74eb6ce84fb1
-- title:
--   Vanishing of GL₃ type integrals for large n₂
-- statement:
--   Let $v$ be a nonzero prime of $\mathbb{Z}$, write $F=\mathbb{Q}_v$ for the completion, and let $\psi_v$ be the inverse of the standard local additive character `psiLocal` of $F$. Let $\chi_0,\chi_1,\chi_2$ be characters $F^\times\to\mathbb{C}^\times$ and $a_0,a_1,a_2$ natural numbers such that each $\chi_i$ is trivial on the higher units of level $a_i$ and nontrivial on the higher units of every level $m<a_i$ (exact conductor exponent $a_i$). Let $W:GL_3(F)\to\mathbb{C}$ be of the form $W=$ `coefficientFn` $\Lambda\,f$, i.e. $W(g)=\Lambda\bigl(f(\cdot\,g)\bigr)$, for some $f$ in the principal series `principalSeries3` attached to $\chi$ (locally constant functions left invariant under upper unipotents and transforming by `torusChar3` times `halfModulus3` under the diagonal torus) and some $\mathbb{C}$-linear $\Lambda$ on that space with $\Lambda$ a $\psi_v$-Whittaker functional, $\Lambda(F(\cdot\,u(x,y,z)))=\psi_v(x+y)\Lambda(F)$. Let $\varpi$ be an element of the valuation ring whose image in $F$ is nonzero of valuation $\exp(-1)$, and let $b$ be a natural number with $2b+1\le a_i$ for all $i$. Then for every $g_3\in GL_3(F)$, every $k_0\in GL_2(F)$, every character $\eta$ of $F^\times$ with exact conductor exponent $c\le b$, and every Haar measure $\mu_2$ on $GL_2(F)$ (for the Borel structure `localGLBorel`), there is an integer $N$ such that for all $(n_1,n_2)\in\mathbb{Z}\times\mathbb{Z}$ with $n_2\ge N$ both of the integrals
--   $$\int_{\{|u|=1\}}\Bigl(\int_{K}W\bigl(\iota(\varpi^{n_2}I_2\cdot\mathrm{diag}(\varpi^{n_1}u,1)\cdot k_0k)\,g_3\bigr)\,d\mu_2(k)\Bigr)\eta(u)\,du,$$
--   $$\int_{\{|u|=1\}}\Bigl(\int_{K}W^{\vee}\bigl(\iota(\varpi^{n_2}I_2\cdot\mathrm{diag}(\varpi^{n_1}u,1)\cdot k_0\,{}^t k^{-1})\bigr)\,d\mu_2(k)\Bigr)\eta(u)\,du$$
--   vanish. Here $\iota$ is the upper-left embedding `iotaGL` of $GL_2$ into $GL_3$, $K$ is the local level subgroup `localLevelOne` at $v^b$, $W^{\vee}(y)=W(w_3\,{}^t y^{-1}g_3)$ is `dualWhittakerFn3` applied to $x\mapsto W(xg_3)$, ${}^tk^{-1}$ is `transposeInvN`, and the outer integral is over the unit group with the measure obtained by pulling back along $u\mapsto u$ the multiplicative measure $|x|^{-1}\,d\mu$ built from the self-dual additive Haar measure `selfDualHaarAt` at $v$.
--
--   This records one dominant-direction half of the assertion that the type integrals of a Whittaker coefficient of a sufficiently ramified $GL_3$ principal series are supported on a finite set of torus shells: only a lower bound on the second exponent $n_2$ is produced, with no constraint on $n_1$. It feeds the finite-support statement [`LanglandsTunnell.CubicInduction.exists_finset_typeIntegral_eq_zero_of_eq_coefficientFn_of_le_conductorExponentAt`](thm.html#LanglandsTunnell.CubicInduction.exists_finset_typeIntegral_eq_zero_of_eq_coefficientFn_of_le_conductorExponentAt) used in the converse-theorem computation of local Rankin–Selberg integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_snd.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse
open scoped nonZeroDivisors
open scoped Classical in

theorem
LanglandsTunnell.CubicInduction.exists_forall_typeIntegral_eq_zero_of_le_snd
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → ℕ)
    (ha : ∀ i, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (χ i) (a i))
    (W : LocalGL3 v → ℂ)
    (hmem : ∃ (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)),
      IsWhittakerFunctional3 ψv Λ ∧ W = coefficientFn Λ f)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ)
    (hfloorb : ∀ i, 2 * b + 1 ≤ a i) :
    ∀ (g₃ : LocalGL3 v) (k₀ : GL (Fin 2) (v.adicCompletion ℚ)) (η : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (c : ℕ),
    LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v η c → c ≤ b →
    letI := localBorel ℚ v
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∃ N : ℤ, ∀ n : ℤ × ℤ, N ≤ n.2 →
        (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                W (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) = 0 ∧
        (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) = 0 := by sorry
