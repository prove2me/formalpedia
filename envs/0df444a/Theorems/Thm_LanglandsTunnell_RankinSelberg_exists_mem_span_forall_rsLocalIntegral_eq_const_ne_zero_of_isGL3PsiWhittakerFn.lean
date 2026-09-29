-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_rsLocalIntegral_eq_const_ne_zero_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.RankinSelberg.exists_mem_span_forall_rsLocalIntegral_eq_const_ne_zero_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/5a0f95bb-233b-5e52-99ea-b7e616bbb304
-- title:
--   Non-degenerate test pair for the local GL₃× GL₂ integral
-- statement:
--   Let $p$ be a prime of $\mathcal{O}_{\mathbb{Q}}$ and write $\psi_p$ for [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65). Let $W_{3,\mathrm{base}}:GL_3(\mathbb{Q}_p)\to\mathbb{C}$ satisfy: $W_{3,\mathrm{base}}(u(x,y,z)g)=\psi_p^{-1}(x+y)\,W_{3,\mathrm{base}}(g)$ for all $x,y,z$ and $g$, where $u(x,y,z)$ is the upper unipotent matrix with entries $x,z,y$ in positions $(1,2),(1,3),(2,3)$; some open subgroup of $GL_3(\mathbb{Q}_p)$ fixes $W_{3,\mathrm{base}}$ under right translation; $W_{3,\mathrm{base}}\neq 0$; and every nonzero $W$ in `gl3CyclicSubspace W₃base` (the $\mathbb{C}$-span of the right translates of $W_{3,\mathrm{base}}$) has $W_{3,\mathrm{base}}$ in its own cyclic subspace. Let $N\neq\bot$ be an ideal and let $w_{2,\mathrm{base}}:GL_2(\mathbb{Q}_p)\to\mathbb{C}$ be nonzero with $w_{2,\mathrm{base}}(n(x)g)=\psi_p(x)w_{2,\mathrm{base}}(g)$ for $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and invariant under right translation by [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding into $GL_2$ of the finite adeles of the finite level-one subgroup of level $N$. Then, for the Borel structure on $GL_2(\mathbb{Q}_p)$, there are $w_2$ in the span of the right translates of $w_{2,\mathrm{base}}$ and $W_3\in$ `gl3CyclicSubspace W₃base` such that for every Haar measure $\mu_2$ on $GL_2(\mathbb{Q}_p)$ and every Haar measure $\mu_{N_2}$ on the image of `unipotentGL2Hom` there is $c\neq 0$ with $$\int (W_3(\iota g)\,w_2(g))\,\lVert\det g\rVert^{s-1/2}\,d\bigl(\mu_2\cdot \mathrm{density}\bigr)=c\quad\text{for all }s\in\mathbb{C},$$ where $\iota$ is the embedding $g\mapsto\operatorname{diag}(g,1)$, $\lVert\cdot\rVert$ is `modulus`, and the measure is $\mu_2$ weighted by the quotient density attached to the unipotent subgroup and $\mu_{N_2}$. The test pair is chosen before the measures; $c$ depends on the measures but not on $s$, and since $c\neq0$ the integrand is in particular integrable.
--
--   This is the local non-degeneracy (test-vector) statement for the $GL_3\times GL_2$ Rankin–Selberg integral at a finite place, in the form of Jacquet–Piatetski-Shapiro–Shalika: a suitable pair of Whittaker vectors makes the local integral an everywhere nonzero constant in $s$. It feeds the assembly of a finite family of local data with nonvanishing Rankin–Selberg integrals used on the converse-theorem side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_mem_span_forall_rsLocalIntegral_eq_const_ne_zero_of_isGL3PsiWhittakerFn.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_mem_span_forall_rsLocalIntegral_eq_const_ne_zero_of_isGL3PsiWhittakerFn
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)

    (N : Ideal (𝓞 ℚ)) (_hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∃ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
    ∃ W₃ ∈ gl3CyclicSubspace W₃base,
      ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∃ c : ℂ, c ≠ 0 ∧
        ∀ s : ℂ,
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s (fun g => W₃ (iotaGL g)) w₂ = c := by sorry
