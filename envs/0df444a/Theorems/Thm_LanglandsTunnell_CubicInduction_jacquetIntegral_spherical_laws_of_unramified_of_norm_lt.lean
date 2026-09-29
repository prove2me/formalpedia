-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetIntegral_spherical_laws_of_unramified_of_norm_lt
-- name    : LanglandsTunnell.CubicInduction.jacquetIntegral_spherical_laws_of_unramified_of_norm_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/edbb42f7-fb7c-5db6-b8a8-aa21f29aebc2
-- title:
--   Jacquet integral of the spherical vector: Casselman–Shalika formula for GL₂
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and let $\varpi$ be an element of the valuation ring of the completion $\mathbb{Q}_v$ whose image in $\mathbb{Q}_v$ is non-zero and has valuation $\exp(-1)$, so a uniformiser. Let $\chi_0,\chi_1\colon \mathbb{Q}_v^\times \to \mathbb{C}^\times$ be group homomorphisms (indexed by `Fin 2`) each trivial on the units of valuation $1$, and write $\alpha_i = \chi_i(\varpi)$; assume $|\alpha_0| < |\alpha_1|$. Let $f\colon \mathrm{GL}_2(\mathbb{Q}_v)\to\mathbb{C}$ lie in `principalSeries2 v χ`, that is: $f$ is locally constant, $f(n(x)g)=f(g)$ for upper unipotent $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and $f(\mathrm{diag}(a_0,a_1)g) = \chi_0(a_0)\chi_1(a_1)\,\sqrt{\|a_0\|/\|a_1\|}\,f(g)$ for $a_0,a_1\in\mathbb{Q}_v^\times$; assume further that $f$ is invariant under right translation by the subgroup [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the preimage at $v$ of the finite adelic level-one subgroup for the unit ideal), and that $f(1)=1$. Let $w_0\in\mathrm{GL}_2(\mathbb{Q}_v)$ have matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Then, for the Borel $\sigma$-algebra on $\mathbb{Q}_v$ and every additive Haar measure $\nu$: for each $g$ the function $y \mapsto f(w_0 n(y) g)\,\psi_v(y)^{-1}$ is integrable, where $\psi_v$ is the local component at $v$ of the standard additive character of $\mathbb{Q}$; and the resulting $J(g)=\int f(w_0 n(y) g)\psi_v(y)^{-1}\,d\nu(y)$ satisfies $J(n(x)g)=\psi_v(x)J(g)$ for all $x,g$; $J(gk)=J(g)$ for $k$ in that level-one subgroup; $J(g\cdot\varpi 1_2)=\alpha_0\alpha_1 J(g)$; $J(1) = \nu(\{y : |y|\le 1\})\bigl(1 - N^{-1}\alpha_0/\alpha_1\bigr)$ with $N =$ `Ideal.absNorm v.asIdeal`; $J(1)\ne 0$; and for every $m\in\mathbb{Z}$, $J(\mathrm{diag}(\varpi^m,1)) = J(1)\cdot$ `torusFactor` $N,\;N^{1/2}(\alpha_0+\alpha_1),\;\alpha_0\alpha_1,\;m$, which is the value at $m$ of the associated Hecke recursion sequence for $m\ge 0$ and $0$ for $m<0$.
--
--   This is the Casselman–Shalika/Shintani computation for $\mathrm{GL}_2$ over a $p$-adic field, carried out in the dominant range $|\alpha_0|<|\alpha_1|$ where the Jacquet integral of the spherical section of the normalised unramified principal series converges absolutely; it records the Whittaker transformation laws, the normalising value $J(1)$ and the values on the diagonal torus in terms of a Hecke recursion. It is used in the construction of the local data entering the Rankin–Selberg local integrals at finite places, in `exists_primalMiddleDatum_rsLocalIntegral_mul_eq_of_iotaGL_invariant_of_dominant` and its dual counterpart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetIntegral_spherical_laws_of_unramified_of_norm_lt.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction
open UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.jacquetIntegral_spherical_laws_of_unramified_of_norm_lt
    (v : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → χ i u = 1)
    (hdom : ‖((χ 0 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)‖ <
      ‖((χ 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)‖)
    (f : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 v χ)
    (hfK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → f (g * k) = f g)
    (hf1 : f 1 = 1)
    (w₀ : GL (Fin 2) (v.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localBorel ℚ v
    ∀ (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      (∀ g : GL (Fin 2) (v.adicCompletion ℚ),
        Integrable (fun y : v.adicCompletion ℚ =>
          f (w₀ * unipotentGL2 y * g) * (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ y) ν) ∧
      let J : GL (Fin 2) (v.adicCompletion ℚ) → ℂ := fun g =>
        ∫ y, f (w₀ * unipotentGL2 y * g) * (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ y ∂ν
      let α₀ : ℂ := ((χ 0 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)
      let α₁ : ℂ := ((χ 1 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)
      (∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
          J (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * J g) ∧
      (∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → J (g * k) = J g) ∧
      (∀ g : GL (Fin 2) (v.adicCompletion ℚ),
          J (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) = α₀ * α₁ * J g) ∧
      J 1 = ((ν {y : v.adicCompletion ℚ | Valued.v y ≤ 1}).toReal : ℂ) *
              (1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹ * α₀ / α₁) ∧
      J 1 ≠ 0 ∧
      (∀ m : ℤ, J (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
          J 1 * torusFactor (Ideal.absNorm v.asIdeal : ℂ)
            ((Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) * (α₀ + α₁)) (α₀ * α₁) m) := by sorry
