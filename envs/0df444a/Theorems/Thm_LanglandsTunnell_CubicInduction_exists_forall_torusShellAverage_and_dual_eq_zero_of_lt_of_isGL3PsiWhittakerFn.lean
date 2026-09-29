-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_torusShellAverage_and_dual_eq_zero_of_lt_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.CubicInduction.exists_forall_torusShellAverage_and_dual_eq_zero_of_lt_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/8a5d2d2f-04aa-57de-afd9-8b6672a2a400
-- title:
--   Lower support bound for torus-shell averages of GL₃ Whittaker data
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$, let $\psi_v$ be a non-trivial additive character of the completion $\mathbb{Q}_v$, and let $W:\mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ satisfy $W(u(x,y,z)g)=\psi_v(x+y)W(g)$ for all $x,y,z\in\mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the upper unipotent matrix with entries $x,y,z$; assume also that $W$ is invariant under right translation by every element of some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$, and let $\varpi$ be an element of the valuation ring with non-zero image of valuation $\exp(-1)$, and $b\in\mathbb{N}$. Then for every $g_3\in\mathrm{GL}_3(\mathbb{Q}_v)$, every $k_0\in\mathrm{GL}_2(\mathbb{Q}_v)$, every character $\eta:\mathbb{Q}_v^\times\to\mathbb{C}^\times$ having conductor exponent $c$ (trivial on the $c$-th higher unit group, non-trivial on the $m$-th for each $m<c$) with $c\le b$, and every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$ for the Borel structure, the two arrays indexed by $n=(n_1,n_2)\in\mathbb{Z}\times\mathbb{Z}$ vanish outside a quadrant: there is $N_1\in\mathbb{Z}$ with $A(n)=A^\vee(n)=0$ whenever $n_1<N_1$ or $n_2<N_1$. Here $A(n)$ is the integral over the units of valuation $1$, against $\eta(u)$ and the multiplicative measure got from the self-dual additive Haar measure by the density $|x|^{-1}$ on $x\neq 0$, of the $\mu_2$-integral over the compact level subgroup $\mathrm{localLevelOne}$ of level $v^b$ (the preimage under the local embedding of the finite-adelic level-one group) of $W\big(\iota(\varpi^{n_2}I_2\cdot\mathrm{diag}(\varpi^{n_1}u,1)\cdot k_0k)\,g_3\big)$, with $\iota$ the embedding of $\mathrm{GL}_2$ in the upper-left corner of $\mathrm{GL}_3$; $A^\vee(n)$ is the same expression with $W(\,\cdot\,g_3)$ replaced by its dual $x\mapsto W\big(g_3\cdot\big)$ composed with $g\mapsto w_3\,{}^t g^{-1}$, evaluated at $\iota(\varpi^{n_2}I_2\cdot\mathrm{diag}(\varpi^{n_1}u,1)\cdot k_0\,{}^t k^{-1})$.
--
--   This is the standard lower bound on the support of a smooth Whittaker function restricted to the diagonal torus, in the form needed for the two shell arrays attached to $W$ and to its dual: both vanish unless each of the two simple-root valuations $n_1,n_2$ is bounded below. It is an input to the rationality statement for these torus-shell averages, [`LanglandsTunnell.CubicInduction.exists_rational_torusShellAverage_and_dual_of_admissible_of_isGL3PsiWhittakerFn`](thm.html#LanglandsTunnell.CubicInduction.exists_rational_torusShellAverage_and_dual_of_admissible_of_isGL3PsiWhittakerFn), in the local theory of the $\mathrm{GL}_3\times\mathrm{GL}_2$ Rankin–Selberg integrals used for cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_torusShellAverage_and_dual_eq_zero_of_lt_of_isGL3PsiWhittakerFn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.CubicInduction.exists_forall_torusShellAverage_and_dual_eq_zero_of_lt_of_isGL3PsiWhittakerFn
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψ : ψv ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ) :
    ∀ (g₃ : LocalGL3 v) (k₀ : GL (Fin 2) (v.adicCompletion ℚ)) (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v η c → c ≤ b →
      letI := localBorel ℚ v
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        let A : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                W (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        let Ad : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        ∃ N₁ : ℤ, ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0 ∧ Ad n = 0 := by sorry
