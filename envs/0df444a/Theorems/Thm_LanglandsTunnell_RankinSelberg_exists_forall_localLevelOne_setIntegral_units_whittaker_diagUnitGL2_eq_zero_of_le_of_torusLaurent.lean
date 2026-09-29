-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_localLevelOne_setIntegral_units_whittaker_diagUnitGL2_eq_zero_of_le_of_torusLaurent
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_localLevelOne_setIntegral_units_whittaker_diagUnitGL2_eq_zero_of_le_of_torusLaurent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/82ee6546-dc15-5120-b75f-5d171e21d685
-- title:
--   Vanishing of deep torus shell integrals
-- statement:
--   Fix a nonzero prime $p$ of $\mathcal O_{\mathbb Q}$, write $F=\mathbb Q_p$ for the completion, let $\theta_0,\chi\colon F^\times\to\mathbb C^\times$ be group homomorphisms with $\chi$ locally constant, and let $N\neq 0$ be an ideal of $\mathcal O_{\mathbb Q}$. Let $w_2\colon \mathrm{GL}_2(F)\to\mathbb C$ be a nonzero function satisfying: $w_2(n(x)g)=\psi_p(x)\,w_2(g)$ for all $x\in F$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p$ is the component at $p$ of the standard adelic additive character of $\mathbb Q$; right invariance $w_2(gk)=w_2(g)$ for $k$ in [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at level $N$, the preimage under the embedding $\mathrm{GL}_2(F)\hookrightarrow \mathrm{GL}_2(\mathbb A_{\mathbb Q}^{\mathrm{fin}})$ at the place $p$ of the level-$N$ congruence subgroup [`NumberField.AdelicLevel.finiteLevelOne`](def/NumberField_AdelicLevel.html#L418); irreducibility of the right-translation span $V=\langle g\mapsto w_2(gh):h\rangle_{\mathbb C}$, in the form that every nonzero $w\in V$ has $w_2$ in the span of its own right translates; admissibility, namely for each open subgroup $U\le\mathrm{GL}_2(F)$ a finite set $B$ of functions spanning all $U$-right-invariant vectors of $V$; and the central character law $w_2(zI\cdot g)=\theta_0(z)w_2(g)$. Let $w_J\in\mathrm{GL}_2(F)$ have matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$, and let $\varpi$ be an element of the valuation ring with nonzero image of valuation $\exp(-1)$, i.e. a uniformiser. Assume the torus hypothesis: for every $w\in V$ there are $P\in\mathbb C[X]$, $m\in\mathbb Z$ and $\sigma_0\in\mathbb R$ such that for $\operatorname{Re}s>\sigma_0$ the function $y\mapsto w(\mathrm{diag}(y,1))\chi(y)|y|^{s-1/2}$ is integrable for the multiplicative measure on $F^\times$ obtained from the self-dual additive Haar measure at $p$ by restricting to $F\setminus\{0\}$ and weighting by $|x|^{-1}$, with integral $(\#(\mathcal O_{\mathbb Q}/p))^{ms}\,P\big((\#(\mathcal O_{\mathbb Q}/p))^{-s}\big)$. The conclusion: for every $w\in V$ there is $n_\star\in\mathbb Z$ such that for all $k$ in [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at level $N=\top$ and all integers $n\ge n_\star$, $$\int_{\{|u|=1\}}\chi(u)\,w\Big(\begin{pmatrix}\varpi^n u&0\\0&1\end{pmatrix}k\Big)\,d^\times u=0,$$ the integral being taken against the same multiplicative measure, over the units of valuation $1$.
--
--   This is the local statement that the shell integrals of a Whittaker vector over the diagonal torus, twisted by $\chi$, vanish for all sufficiently deep shells $|y|=q^{-n}$, uniformly in the right translation by the level-one group: the Laurent-polynomial shape of the twisted torus zeta integrals forces its coefficients to terminate. It feeds the Rankin–Selberg input of the converse-theorem step, being cited by [`LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_localLevelOne_setIntegral_units_whittaker_diagUnitGL2_eq_zero_of_le_of_torusLaurent.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
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

theorem LanglandsTunnell.RankinSelberg.exists_forall_localLevelOne_setIntegral_units_whittaker_diagUnitGL2_eq_zero_of_le_of_torusLaurent
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)

    (htorus : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P : Polynomial ℂ) (m : ℤ) (σ₀ : ℝ),
        ∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    :
    letI := localBorel ℚ p
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ nstar : ℤ, ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ n : ℤ, nstar ≤ n →
        ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            ((χ u : ℂˣ) : ℂ) *
              w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u) * k)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) = 0 := by sorry
