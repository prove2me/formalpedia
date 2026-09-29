-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_apply_of_finite
-- name    : LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_apply_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/121be70a-1fbe-5c94-9356-c8886777effc
-- title:
--   Local Rankin–Selberg integrals evaluating a finite Whittaker family
-- statement:
--   Let $p$ be a nonzero prime ideal of $\mathbb{Z}=\mathcal O_{\mathbb Q}$, write $\mathbb Q_p$ for the completion $\mathbb Q_{(p)}$ and $\psi_p$ for the local standard additive character `psiLocal ℚ p`. Let $W_3^{\mathrm{base}}:\mathrm{GL}_3(\mathbb Q_p)\to\mathbb C$ satisfy: the Whittaker transformation law $W_3^{\mathrm{base}}\big(u(x,y,z)g\big)=\psi_p(x+y)^{-1}W_3^{\mathrm{base}}(g)$ for all $x,y,z$ and all $g$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x,y,z$; right invariance under some open subgroup of $\mathrm{GL}_3(\mathbb Q_p)$; $W_3^{\mathrm{base}}\neq 0$; the irreducibility condition that every nonzero $W$ in the cyclic space `gl3CyclicSubspace W₃base` (the $\mathbb C$-span of the right translates of $W_3^{\mathrm{base}}$) has $W_3^{\mathrm{base}}$ in its own cyclic space; and the admissibility condition that for every open subgroup $U_v$ there is a finite set $B$ of functions whose $\mathbb C$-span contains every $U_v$-right-invariant element of the cyclic space. Fix $g_0\in\mathrm{GL}_2(\mathbb Q_p)$, a type $\iota$, a finite subset $t\subseteq\iota$ and functions $u_i:\mathrm{GL}_2(\mathbb Q_p)\to\mathbb C$ such that for $i\in t$ one has $u_i\big(n(x)g\big)=\psi_p(x)\,u_i(g)$ for the unipotent $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and each $u_i$ is right invariant under some open subgroup. Then, with $\mathrm{GL}_2(\mathbb Q_p)$ carrying its Borel structure, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb Q_p)$ and every Haar measure $\mu_{N_2}$ on the image subgroup of `unipotentGL2Hom` there exist $W_3$ in the cyclic space of $W_3^{\mathrm{base}}$ and a constant $c\neq 0$, independent of $i$ and $s$, such that for all $i\in t$ and all $s\in\mathbb C$ the function $g\mapsto W_3(\iota(g))\,u_i(g)\,|\det g|_p^{\,s-1/2}$, with $\iota$ the block embedding $g\mapsto\mathrm{diag}(g,1)$ of $\mathrm{GL}_2$ into $\mathrm{GL}_3$ and $|\cdot|_p$ the module `modulus`, is integrable for $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) attached to the unipotent subgroup and $\mu_{N_2}$, and the local Rankin–Selberg integral `rsLocalIntegral` of that data — the integral of the same integrand against that weighted measure, with $\delta(g)=|\det g|_p$ — equals $c\,|\det g_0|_p^{\,s-1/2}\,u_i(g_0)$.
--
--   This is the local "bump" construction at a finite place: a single vector in the Whittaker model of the $\mathrm{GL}_3$ representation, together with one nonzero constant, makes the local Rankin–Selberg integral against each member of a prescribed finite family of $\mathrm{GL}_2$ Whittaker functions reduce to the monomial $|\det g_0|_p^{s-1/2}$ times evaluation at the point $g_0$. It is obtained from the corresponding statement with an integral of $u$ over a compact open subgroup, and is used in the converse-theorem part of the Langlands–Tunnell argument, where nonvanishing of global integrals at prescribed translates must be forced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_apply_of_finite.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_apply_of_finite
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
    {ι : Type} (t : Finset ι) (u : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hulaw : ∀ i ∈ t, ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      u i (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * u i g)
    (husm : ∀ i ∈ t, ∃ U' : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U' : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U', ∀ g : GL (Fin 2) (p.adicCompletion ℚ), u i (g * k) = u i g) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∃ W₃ ∈ gl3CyclicSubspace W₃base, ∃ c : ℂ, c ≠ 0 ∧
        ∀ i ∈ t, ∀ s : ℂ,
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (W₃ (iotaGL g) * u i g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s (fun g => W₃ (iotaGL g)) (u i) =
            c * ((modulus ((Matrix.GeneralLinearGroup.det g₀ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) *
              u i g₀ := by sorry
