-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_apply_diagZ_mul_scalarPi_pow_eq_ite_of_forall_rsLocalIntegral_spherical_eq_measure
-- name    : LanglandsTunnell.RankinSelberg.forall_apply_diagZ_mul_scalarPi_pow_eq_ite_of_forall_rsLocalIntegral_spherical_eq_measure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/31ff732e-e836-541e-ad07-aad44d2935f9
-- title:
--   Spherical Rankin–Selberg periods determine torus values
-- statement:
--   Let $v$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, and let $\varpi$ lie in the valuation ring of $v$ with nonzero image $\pi$ in the completion $\mathbb{Q}_v$ and $\mathrm{v}(\pi)=\exp(-1)$, so $\pi$ is a uniformiser. Let $f:\mathrm{GL}_2(\mathbb{Q}_v)\to\mathbb{C}$ satisfy: $f(u(x)g)=\psi_v(x)^{-1}f(g)$ for $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, where $\psi_v$ is the standard local additive character obtained from the standard adelic character through the place-$v$ inclusion; $f(gk)=f(g)$ for $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding into $\mathrm{GL}_2$ of the finite adeles of the adelic level-one subgroup of level the unit ideal; and $f(\mathrm{diag}(\pi^{m-n},1)\cdot(\pi I)^n)=0$ whenever $n<0$ or $m<n$. Assume further: for all $a_1,a_2\in\mathbb{C}$ with $a_1a_2\neq 0$ and every $W_2:\mathrm{GL}_2(\mathbb{Q}_v)\to\mathbb{C}$ with $W_2(u(x)g)=\psi_v(x)W_2(g)$, right invariant under the same level-one subgroup, $W_2(1)=1$, $W_2(g\cdot\pi I)=(a_1a_2/q)W_2(g)$ with $q=\mathrm{absNorm}\,v$, and $W_2(\mathrm{diag}(\pi^m,1))=\mathrm{torusFactor}(q,a_1+a_2,a_1a_2/q,m)$ (the Hecke recursion sequence for $m\ge 0$, zero otherwise), and for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$ (Borel structure) and Haar measure $\mu_N$ on the image of `unipotentGL2Hom`, there is $\sigma_2\in\mathbb{R}$ such that for $\mathrm{Re}\,s>\sigma_2$ the function $g\mapsto f(g)W_2(g)\,|\det g|^{s-1/2}$ is integrable for $\mu_2$ weighted by [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup, and `rsLocalIntegral` of $f$ against $W_2$ with $\delta=|\det|$ equals the measure, for that weighted measure, of $\{g=nk: n\in N,\ k\in\text{level-one}\}$. Then $f(\mathrm{diag}(\pi^{m-n},1)(\pi I)^n)=1$ if $m=n=0$ and $0$ otherwise, for all $m,n\in\mathbb{Z}$.
--
--   This is the unramified Kirillov/Satake-inversion step on $\mathrm{GL}_2$: matching the local Rankin–Selberg period of $f$ against every normalised spherical $\psi_v$-Whittaker function with the volume of $N\,\mathrm{GL}_2(\mathbb{Z}_v)$ pins down the values of $f$ on the diagonal torus, forcing $f$ to be the characteristic-type function of the identity cell. It is used in the construction of the local bump vector in the converse-theorem input of the Langlands–Tunnell argument, in particular by `exists_mem_gl3CyclicSubspace_congruenceK1_invariant_iotaGL_eq_bump_of_localZeta31_fe_one`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_apply_diagZ_mul_scalarPi_pow_eq_ite_of_forall_rsLocalIntegral_spherical_eq_measure.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction
  LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker

theorem LanglandsTunnell.RankinSelberg.forall_apply_diagZ_mul_scalarPi_pow_eq_ite_of_forall_rsLocalIntegral_spherical_eq_measure
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ϖ : v.adicCompletionIntegers ℚ)
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

    (f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hfψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      f (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * f g)
    (hfK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → f (g * k) = f g)
    (hsupp : ∀ m n : ℤ, (n < 0 ∨ m < n) →
      f (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (m - n) * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n) = 0)

    (hid : ∀ (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0)
        (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
        (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
          W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
        (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
        (hW₂1 : W₂ 1 = 1)
        (hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
          W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
            a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
        (hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
          torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m),
        letI := localGLBorel ℚ v
        haveI := borelSpace_localGLBorel ℚ v
        ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
          (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
        ∃ σ₂ : ℝ,
          (∀ s : ℂ, σ₂ < s.re →
            Integrable
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (f g * W₂ g) *
                  ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                      v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
                (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
                s f W₂ =
              (((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
                  {g : GL (Fin 2) (v.adicCompletion ℚ) |
                    ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ))) :
    ∀ m n : ℤ, f (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (m - n) * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n) = if m = 0 ∧ n = 0 then 1 else 0 := by sorry
