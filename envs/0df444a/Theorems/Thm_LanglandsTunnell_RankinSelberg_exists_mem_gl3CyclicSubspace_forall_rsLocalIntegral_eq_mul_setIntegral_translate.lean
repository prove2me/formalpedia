-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_setIntegral_translate
-- name    : LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_setIntegral_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/74605ea1-8a74-53b8-b5e5-b8f6ed2b00a3
-- title:
--   Bump test vector for the local GL₃× GL₂ Rankin–Selberg integral
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_p$ and standard local additive character $\psi_p$. Let $W_{3}^{\mathrm{base}} : GL_3(\mathbb{Q}_p) \to \mathbb{C}$ satisfy: $W_{3}^{\mathrm{base}}(n(x,y,z)g) = \psi_p^{-1}(x+y)\,W_{3}^{\mathrm{base}}(g)$ for all $x,y,z$ and $g$, where $n(x,y,z)$ is the upper triangular unipotent matrix with entries $x,y,z$; right invariance under some open subgroup of $GL_3(\mathbb{Q}_p)$; $W_{3}^{\mathrm{base}} \neq 0$; every nonzero $W$ in the cyclic subspace $\langle W_{3}^{\mathrm{base}}\rangle$ spanned by the right translates of $W_{3}^{\mathrm{base}}$ has $W_{3}^{\mathrm{base}}$ in its own cyclic subspace; and, for each open subgroup $U_v \le GL_3(\mathbb{Q}_p)$, the $U_v$-right-invariant vectors of $\langle W_{3}^{\mathrm{base}}\rangle$ lie in the span of a finite set of functions. Let $g_0 \in GL_2(\mathbb{Q}_p)$ and let $U \le GL_2(\mathbb{Q}_p)$ be a subgroup that is open and compact as a set, such that $\psi_p(x) = 1$ whenever $g_0^{-1}n(x)g_0 \in U$, $n(x)$ the upper unipotent matrix. Then, for every Haar measure $\mu_2$ on $GL_2(\mathbb{Q}_p)$ (with its Borel structure) and every Haar measure $\mu_{N_2}$ on the image $N_2$ of the unipotent homomorphism, there are $W_3 \in \langle W_{3}^{\mathrm{base}}\rangle$ and $c \neq 0$ such that for every $u : GL_2(\mathbb{Q}_p) \to \mathbb{C}$ with $u(n(x)g) = \psi_p(x)u(g)$ and right invariant under some open subgroup, and every $s \in \mathbb{C}$: the function $g \mapsto W_3(\iota g)\,u(g)\,|\det g|^{s-1/2}$, where $\iota$ is the upper-left block embedding $GL_2 \hookrightarrow GL_3$ and $|\cdot|$ is the modulus, is integrable for $\mu_2$ weighted by the quotient density of $N_2$ relative to $\mu_{N_2}$, and the local Rankin–Selberg integral of the pair $(W_3 \circ \iota, u)$ with modulus character $|\det\,\cdot\,|$ at $s$ equals $c\,|\det g_0|^{s-1/2}\int_U u(g_0k)\,d\mu_2(k)$.
--
--   This produces the test vector in the $GL_3$ Whittaker model whose local Rankin–Selberg pairing against an arbitrary smooth $\psi_p$-Whittaker function on $GL_2(\mathbb{Q}_p)$ collapses to a monomial in $|\det g_0|$ times the average of that function over the coset $g_0U$ — the bottom piece of the Bernstein–Zelevinsky filtration in the form needed to separate local data. It feeds the finite-place input of the converse-theorem argument, being cited by [`LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_apply_of_finite`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_apply_of_finite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_setIntegral_translate.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_setIntegral_translate
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₃base : LocalGL3 p → ℂ)
    (hW₃law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₃base)
    (hW₃sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₃base (g * k) = W₃base g)
    (hW₃ne : W₃base ≠ 0)
    (hW₃irr : ∀ W ∈ gl3CyclicSubspace W₃base, W ≠ 0 → W₃base ∈ gl3CyclicSubspace W)

    (hW₃adm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ W ∈ gl3CyclicSubspace W₃base,
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)))

    (g₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
    (hUo : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ)))) (hUc : IsCompact (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hψU : ∀ x : p.adicCompletion ℚ, g₀⁻¹ * unipotent x * g₀ ∈ U → NumberField.StandardAddChar.psiLocal ℚ p x = 1) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∃ W₃ ∈ gl3CyclicSubspace W₃base, ∃ c : ℂ, c ≠ 0 ∧
        ∀ (u : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
          (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
            u (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * u g) →
          (∃ U' : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U' : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
            ∀ k ∈ U', ∀ g : GL (Fin 2) (p.adicCompletion ℚ), u (g * k) = u g) →
          ∀ s : ℂ,
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (W₃ (iotaGL g) * u g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W₃ (iotaGL g)) u =
              c * ((modulus ((Matrix.GeneralLinearGroup.det g₀ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) *
                ∫ k in (U : Set (GL (Fin 2) (p.adicCompletion ℚ))), u (g₀ * k) ∂μ₂ := by sorry
