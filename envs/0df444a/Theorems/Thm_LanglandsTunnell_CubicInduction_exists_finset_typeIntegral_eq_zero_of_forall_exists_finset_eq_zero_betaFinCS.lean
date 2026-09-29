-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_typeIntegral_eq_zero_of_forall_exists_finset_eq_zero_betaFinCS
-- name    : LanglandsTunnell.CubicInduction.exists_finset_typeIntegral_eq_zero_of_forall_exists_finset_eq_zero_betaFinCS
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/f46cdbb3-ffc2-58ac-8ca8-de94a77054d0
-- title:
--   Vanishing of type integrals outside finitely many torus shells
-- statement:
--   Let $v$ be a nonzero prime of $\mathcal{O}_{\mathbb{Q}}$, let $W\colon \mathrm{GL}_3(\mathbb{Q}_v)\to\mathbb{C}$ be a function, let $\varpi$ lie in the valuation ring of $\mathbb{Q}_v$ with nonzero image $\pi$ in $\mathbb{Q}_v$, and let $b$ be a natural number. Write $\iota$ for the embedding $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$ as the upper-left block with last diagonal entry $1$, $t(n_1,n_2,u)=\mathrm{diag}(\pi,\pi)^{n_2}\,\mathrm{diag}(\pi^{n_1}u,1)$ for $(n_1,n_2)\in\mathbb{Z}^2$ and $u\in\mathbb{Q}_v^\times$, and $W^{\mathrm d}(x)=W(w_3\,{}^{t}x^{-1})$ with $w_3$ the antidiagonal permutation matrix. Assume that for each $g\in\mathrm{GL}_3(\mathbb{Q}_v)$ there is a finite $S\subset\mathbb{Z}^2$ with $W(\iota(t(n_1,n_2,u))kg)=0$ and $W^{\mathrm d}(\iota(t(n_1,n_2,u))kg)=0$ for all $(n_1,n_2)\notin S$, all $k$ in the subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$ whose matrix and inverse have all entries of valuation $\le 1$, and all units $u$ with $|u|=1$. The conclusion: for every $g_3\in\mathrm{GL}_3(\mathbb{Q}_v)$, every $k_0\in\mathrm{GL}_2(\mathbb{Q}_v)$, every character $\eta\colon\mathbb{Q}_v^\times\to\mathbb{C}^\times$ having conductor exponent $c$ in the sense that $\eta$ is trivial on the $c$-th higher unit group while for each $m<c$ some element of the $m$-th higher unit group is not killed by $\eta$, with $c\le b$, and every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$ for its Borel structure, there is a single finite $T\subset\mathbb{Z}^2$ such that for all $(n_1,n_2)\notin T$ both of the integrals $$\int_{|u|=1}\Big(\int_{K}W\big(\iota(t(n_1,n_2,u)\,k_0k)\,g_3\big)\,\mathrm{d}\mu_2(k)\Big)\eta(u)\,\mathrm{d}\mu^\times(u),\qquad \int_{|u|=1}\Big(\int_{K}\big(x\mapsto W(xg_3)\big)^{\mathrm d}\big(\iota(t(n_1,n_2,u)\,(k_0\cdot{}^{t}k^{-1}))\big)\,\mathrm{d}\mu_2(k)\Big)\eta(u)\,\mathrm{d}\mu^\times(u)$$ vanish, where $K$ is the subgroup of $\mathrm{GL}_2(\mathbb{Q}_v)$ pulled back from the finite-adelic level-one subgroup of level $v^b$ along the local embedding, and $\mu^\times$ is the measure on $\mathbb{Q}_v^\times$ obtained by restricting the self-dual additive Haar measure to $\mathbb{Q}_v\setminus\{0\}$, weighting by the inverse of the modulus, and pulling back along $u\mapsto u$.
--
--   This is the finiteness statement for the shallow type integrals of a function on $\mathrm{GL}_3(\mathbb{Q}_v)$ whose torus-shell support, and that of its Weyl dual, is finite after each right translation — the behaviour of Whittaker functions of a supercuspidal local component. It feeds the Rankin–Selberg functional-equation step of the cubic induction, where only finitely many cells of the torus decomposition contribute to the local zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_finset_typeIntegral_eq_zero_of_forall_exists_finset_eq_zero_betaFinCS.lean

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
LanglandsTunnell.CubicInduction.exists_finset_typeIntegral_eq_zero_of_forall_exists_finset_eq_zero_betaFinCS
    (v : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 v → ℂ)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (b : ℕ)
    (hcs : ∀ g : LocalGL3 v, ∃ S : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ S →
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
        W (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                ^ n.1 * u)) * k * g) = 0 ∧
        dualWhittakerFn3 W (iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
              diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                ^ n.1 * u)) * k * g) = 0) :
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
