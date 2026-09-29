-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/d2b8e938-658c-587f-a416-c432d10bbc3b
-- title:
--   Vanishing of deep torus shells in the unfolded zeta integrand
-- statement:
--   Fix a maximal ideal $p$ of the ring of integers of $\mathbb{Q}$, write $F = \mathbb{Q}_p$ for the completion and $\psi =$ `psiLocal` for the standard local additive character, and let $\theta_0 \colon F^{\times} \to \mathbb{C}^{\times}$ be a character. Let $N \neq 0$ be an ideal and let $w_2 \colon \mathrm{GL}_2(F) \to \mathbb{C}$ be a function with: $w_2(u(x)g) = \psi(x) w_2(g)$ for $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$; right invariance under [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at level $N$ (the pullback along the local embedding of the adelic level-one subgroup); $w_2 \neq 0$; the condition that every nonzero element of the span $V$ of the right translates $g \mapsto w_2(gh)$ generates $w_2$ in the same manner; and admissibility, namely for each open subgroup $U$ a finite subset of functions spanning the $U$-right-invariant vectors of $V$. Assume $w_2(zg) = \theta_0(z) w_2(g)$ for scalar $z$, fix $w_J \in \mathrm{GL}_2(F)$ with matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$, and a locally constant character $\chi \colon F^{\times} \to \mathbb{C}^{\times}$. Assume the torus hypothesis: for each $v \in V$ there are a polynomial $P$, an integer $m$ and $\sigma_0 \in \mathbb{R}$ such that for $\operatorname{Re} s > \sigma_0$ the function $y \mapsto v(\mathrm{diag}(y,1))\chi(y)\lvert y\rvert^{s-1/2}$ is integrable for the multiplicative measure induced by the self-dual Haar measure and its integral equals $q^{ms} P(q^{-s})$, $q = \lvert\mathcal{O}/p\rvert$. Let $\varpi$ be an integral element with nonzero image and valuation $q^{-1}$. Then for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every $w \in V$ and every locally constant compactly supported $\Phi \colon M_2(F) \to \mathbb{C}$, there exist integers $n_\star$ and $c$ such that for all $n_1 \geq n_\star$ with $n_1 + n_2 \geq c$ and all $s \in \mathbb{C}$, writing $a = \varpi^{n_2}\,\mathrm{diag}(\varpi^{n_1},1)$,
--   $$\int_{k} \Bigl(\int_F \psi(x)\,\Phi(u(x)\,a k)\,dx\Bigr)\, \chi(\det(ak))\, w(ak)\, \lvert\det(ak)\rvert^{s}\, d\mu_2(k) = 0,$$
--   the outer integral being over the level-one subgroup at the unit ideal, and $\lvert\cdot\rvert$ the module `modulus`.
--
--   This isolates the deep shells in the Iwasawa-coordinate expansion of the local Godement–Jacquet zeta integral of a Whittaker vector twisted by $\chi$: once the row slice $\Phi \mapsto \int_F \psi(x)\Phi(u(x)\,\cdot)\,dx$ has become independent of the torus parameter, averaging over the diagonal units inside the maximal compact annihilates the term. It feeds the Laurent-expansion statement `forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent`, where only finitely many shells then contribute.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le.lean

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

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.RankinSelberg
open MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le
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
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
          ∃ nstar c : ℤ, ∀ (n₁ n₂ : ℤ), nstar ≤ n₁ → c ≤ n₁ + n₂ → ∀ s : ℂ,
            ∫ k in (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))),
              (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                  Φ ((unipotent x * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n₁ * k) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
                ((χ (Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n₁ * k)) : ℂˣ) : ℂ) *
                w (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n₁ * k) *
                ((modulus ((Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n₁ * k) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s ∂μ₂ = 0 := by sorry
