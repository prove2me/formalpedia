-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_typeIntegral_eq_zero_of_eq_coefficientFn_of_le_conductorExponentAt
-- name    : LanglandsTunnell.CubicInduction.exists_finset_typeIntegral_eq_zero_of_eq_coefficientFn_of_le_conductorExponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/f1543212-f4e9-50ee-9b3c-5a90aac1bcea
-- title:
--   Finite support of the GL₃ Whittaker type integrals
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$ and let $\psi_v$ be the inverse of the standard local additive character of $\mathbb{Q}_v$. Let $\chi_0,\chi_1,\chi_2$ be continuous characters $\mathbb{Q}_v^\times \to \mathbb{C}^\times$ and $a_0,a_1,a_2$ natural numbers such that $\chi_i$ is trivial on the higher units of level $a_i$ while for each $m < a_i$ some unit in the higher units of level $m$ is not killed by $\chi_i$. Let $W : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ be assumed to be of the form $g \mapsto \Lambda(g\cdot f)$ for some $f$ in `principalSeries3` — the space of locally constant functions on $\mathrm{GL}_3(\mathbb{Q}_v)$ invariant under left translation by upper unipotents and transforming under the diagonal torus by $\chi = (\chi_0,\chi_1,\chi_2)$ times the half modulus — and some $\mathbb{C}$-linear functional $\Lambda$ on that space satisfying $\Lambda(u(x,y,z)\cdot F) = \psi_v(x+y)\,\Lambda(F)$. Let $\varpi$ be an element of the valuation ring whose image in $\mathbb{Q}_v$ is nonzero of valuation $\exp(-1)$, and let $b$ be a natural number with $2b+1 \le a_i$ for every $i$. The assertion is: for every $g_3 \in \mathrm{GL}_3(\mathbb{Q}_v)$, every $k_0 \in \mathrm{GL}_2(\mathbb{Q}_v)$, every character $\eta$ of $\mathbb{Q}_v^\times$ whose conductor exponent $c$ (in the same sense as above) satisfies $c \le b$, and every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$ with respect to the Borel structure, there is a finite set $T \subseteq \mathbb{Z} \times \mathbb{Z}$ such that for every $n = (n_1,n_2) \notin T$ both of the following vanish: first, the integral over the units $u$ of valuation $1$, against $\eta(u)$ and the measure obtained by pulling back along $u \mapsto u$ the measure $|x|^{-1}\,dx$ attached to the self-dual Haar measure at $v$, of the $\mu_2$-integral over $k$ in the level subgroup [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) of level $v^b$ of $W\big(\iota(\varpi^{n_2}I_2 \cdot \mathrm{diag}(\varpi^{n_1}u,1) \cdot (k_0 k))\, g_3\big)$, where $\iota$ is the upper-left embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$; and second, the same double integral with the integrand replaced by the dual Whittaker function of $x \mapsto W(x g_3)$, namely $y \mapsto W(w_3\,{}^{t}y^{-1} g_3)$ for the long Weyl element $w_3$, evaluated at $\iota(\varpi^{n_2}I_2 \cdot \mathrm{diag}(\varpi^{n_1}u,1)\cdot (k_0 \cdot {}^{t}k^{-1}))$.
--
--   This is the finiteness half of the local Rankin–Selberg cell decomposition for a Whittaker coefficient of a principal series of $\mathrm{GL}_3(\mathbb{Q}_v)$ whose inducing characters are deep relative to the level $v^b$: all but finitely many torus cells $(n_1,n_2)$ contribute zero to both the type integral and its dual. It is used in the global Rankin–Selberg computation of the $\mathrm{GL}_3 \times \mathrm{GL}_2$ zeta integral, where the sums over cells must be reduced to finite sums before the functional equation and root-number monomial are identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_finset_typeIntegral_eq_zero_of_eq_coefficientFn_of_le_conductorExponentAt.lean

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
LanglandsTunnell.CubicInduction.exists_finset_typeIntegral_eq_zero_of_eq_coefficientFn_of_le_conductorExponentAt
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
      ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
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
