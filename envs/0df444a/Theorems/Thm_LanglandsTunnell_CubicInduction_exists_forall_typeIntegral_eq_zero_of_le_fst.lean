-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst
-- name    : LanglandsTunnell.CubicInduction.exists_forall_typeIntegral_eq_zero_of_le_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/91367457-66c3-5c77-af91-1eb101f76844
-- title:
--   Type integrals of deep GL₃ Whittaker coefficients vanish eventually
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and let $\psi_v$ be the inverse of the standard local additive character `psiLocal` of the completion $\mathbb{Q}_v$. Let $\chi_0,\chi_1,\chi_2$ be homomorphisms $\mathbb{Q}_v^\times \to \mathbb{C}^\times$ and $a_0,a_1,a_2$ natural numbers such that each $\chi_i$ is trivial on the higher unit group of level $a_i$ while for every $m < a_i$ some unit in the higher unit group of level $m$ has $\chi_i \neq 1$. Let $W : GL_3(\mathbb{Q}_v)\to\mathbb{C}$ be of the form $W =$ `coefficientFn` $\Lambda f$ for some $f$ in the principal series `principalSeries3` $v\,\chi$ (locally constant functions invariant under the upper unipotent subgroup and transforming by $\chi$ times the half modulus under the diagonal torus) and some linear functional $\Lambda$ on that space which is $\psi_v$-Whittaker, i.e. $\Lambda$ of the right translate by `upperUnipotent3` $x\,y\,z$ of $F$ equals $\psi_v(x+y)\Lambda F$; thus $W(g) = \Lambda(g\cdot f)$. Let $\varpi$ be an element of the valuation ring with nonzero image of valuation $\exp(-1)$, i.e. a uniformiser, and let $b$ be a natural number with $2b+1 \le a_i$ for all $i$. Then for every $g_3 \in GL_3(\mathbb{Q}_v)$, every $k_0 \in GL_2(\mathbb{Q}_v)$, every character $\eta$ of $\mathbb{Q}_v^\times$ having exact conductor exponent $c$ in the above sense with $c \le b$, and every Haar measure $\mu_2$ on $GL_2(\mathbb{Q}_v)$ for the Borel structure `localGLBorel`, there is an integer $N$ such that for all pairs $n = (n_1,n_2) \in \mathbb{Z}\times\mathbb{Z}$ with $n_1 \ge N$ both of the following integrals vanish: first, the integral over the units $u$ of valuation $1$, against the measure obtained by pulling back along $\mathbb{Q}_v^\times \to \mathbb{Q}_v$ the multiplicative measure $|x|^{-1}\,dx$ attached to the self-dual additive Haar measure `selfDualHaarAt`, of $\eta(u)$ times the $\mu_2$-integral over $k$ in the compact open subgroup `localLevelOne` of level $v^b$ (the preimage under the local embedding of the finite-adelic level-one subgroup) of $W\bigl(\iota(\varpi^{n_2}I_2 \cdot \mathrm{diag}(\varpi^{n_1}u,1)\cdot k_0k)\,g_3\bigr)$, where $\iota$ is the upper-left embedding `iotaGL` of $GL_2$ in $GL_3$; second, the same double integral with the inner integrand replaced by the value at $\iota(\varpi^{n_2}I_2\cdot\mathrm{diag}(\varpi^{n_1}u,1)\cdot k_0\,{}^t k^{-1})$ of the dual `dualWhittakerFn3` of $x \mapsto W(xg_3)$, i.e. of $y \mapsto W(w_3\,{}^ty^{-1}g_3)$, with $w_3$ the long Weyl element.
--
--   This is the local Jacquet-module input to the type-integral analysis of the $GL_3$ principal series at a place where the inducing characters have conductor exponents large compared with the level $b$: the $K_1(v^b)$-average followed by the $\eta$-weighted average over the units vanishes once the first torus coordinate is large. It is one dominant-direction half of the statement that such type integrals vanish outside a finite set of shells, and is cited in the assembly of that finiteness statement, [`LanglandsTunnell.CubicInduction.exists_finset_typeIntegral_eq_zero_of_eq_coefficientFn_of_le_conductorExponentAt`](thm.html#LanglandsTunnell.CubicInduction.exists_finset_typeIntegral_eq_zero_of_eq_coefficientFn_of_le_conductorExponentAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst.lean

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
LanglandsTunnell.CubicInduction.exists_forall_typeIntegral_eq_zero_of_le_fst
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
      ∃ N : ℤ, ∀ n : ℤ × ℤ, N ≤ n.1 →
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
