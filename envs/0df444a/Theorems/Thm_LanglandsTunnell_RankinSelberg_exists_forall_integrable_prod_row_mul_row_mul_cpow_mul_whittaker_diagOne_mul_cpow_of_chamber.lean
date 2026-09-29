-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_prod_row_mul_row_mul_cpow_mul_whittaker_diagOne_mul_cpow_of_chamber
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_prod_row_mul_row_mul_cpow_mul_whittaker_diagOne_mul_cpow_of_chamber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/b132194e-0043-5904-93e8-17bf0cd97468
-- title:
--   Product integrability of the local Rankin–Selberg kernel in a chamber
-- statement:
--   Fix a nonzero prime $p$ of the integers of $\mathbb Q$ and write $F=\mathbb Q_p$ for the $p$-adic completion. Let $\chi_0,\chi_1:F^\times\to\mathbb C^\times$ be locally constant characters and $\sigma_0,\sigma_1\in\mathbb R$ with $|\chi_i(a)|=\|a\|^{\sigma_i}$ for all $a$, and assume $\sigma_1<\sigma_0$. Let $\Phi_1,\Phi_2:F^2\to\mathbb C$ be locally constant with compact support. Let $\theta_0:F^\times\to\mathbb C^\times$ be a character, $N$ a nonzero ideal, and $w_{2}:\mathrm{GL}_2(F)\to\mathbb C$ a function subject to: the Whittaker law $w_2(u(x)g)=\psi_p(x)\,w_2(g)$ for the local component $\psi_p$ of the standard additive character and $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; right invariance under the group of elements of $\mathrm{GL}_2(F)$ whose image under the local embedding lies in the level-$N$ congruence subgroup of $\mathrm{GL}_2$ of the finite adeles; $w_2\neq 0$; an irreducibility condition, namely that every nonzero element $w$ of the span $V$ of the right translates $g\mapsto w_2(gh)$ has $w_2$ in the span of the right translates of $w$; an admissibility condition, namely that for every open subgroup $U$ the right $U$-invariant vectors of $V$ lie in the span of a finite set; and the central character law $w_2(zI\cdot g)=\theta_0(z)w_2(g)$. Then, with $F$ and $\mathrm{GL}_2(F)$ carrying their Borel structures, for every $w\in V$ there is a $\sigma_P\in\mathbb R$ such that for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$ and every $s$ with $\operatorname{Re}s>\sigma_P$ the function $$(g,y)\mapsto \Phi_1(g_{(0)})\,\Phi_2(g_{(1)})\,\chi_0(\det g)\,|\det g|^{s+1/2}\cdot w(\mathrm{diag}(y,1)g)\,\chi_1(y)\,|y|^{s-1/2}$$ (where $g_{(0)},g_{(1)}$ are the rows of $g$ and $|\cdot|$ is the module of the local field, equal to the norm) is integrable on $\mathrm{GL}_2(F)\times F^\times$ for the product of $\mu_2$ with the multiplicative measure $\|x\|^{-1}dx$ on $F\setminus\{0\}$ pulled back to $F^\times$, $dx$ being the self-dual additive Haar measure at $p$.
--
--   This is the genuine product integrability on $\mathrm{GL}_2(F)\times F^\times$, in the chamber $\sigma_1<\sigma_0$ and for $\operatorname{Re}s$ large, of the kernel whose unfolding produces the local Rankin–Selberg integral attached to a Whittaker vector and a Godement section. It serves as the Fubini hypothesis for the unfolding step, and is invoked in the derivation of the Laurent-type functional equation of the local Rankin–Selberg integrals, both in the Borel-eigenfunctional and in the cuspidal case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_prod_row_mul_row_mul_cpow_mul_whittaker_diagOne_mul_cpow_of_chamber.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_prod_row_mul_row_mul_cpow_mul_whittaker_diagOne_mul_cpow_of_chamber
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((χ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (Φ₁ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ₁ : IsLocallyConstant Φ₁ ∧ HasCompactSupport Φ₁)
    (Φ₂ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)

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
    :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ σP : ℝ, ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (s : ℂ), σP < s.re →
        Integrable (fun q : GL (Fin 2) (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ =>
            Φ₁ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0) * Φ₂ ((q.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1) *
                ((χ 0 (Matrix.GeneralLinearGroup.det q.1) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det q.1 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) *
              (w (diagOne q.2 * q.1) * ((χ 1 q.2 : ℂˣ) : ℂ) * ((modulus (q.2 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)))
          (μ₂.prod (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) := by sorry
