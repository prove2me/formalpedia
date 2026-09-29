-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_normPowChar_godementSection_abs_mem_principalSeries2_of_lt
-- name    : LanglandsTunnell.RankinSelberg.exists_normPowChar_godementSection_abs_mem_principalSeries2_of_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/12ed65cf-e4e7-5db5-a9a4-b7ac7ac77da7
-- title:
--   Non-negative Godement section for real norm-power characters
-- statement:
--   Let $p$ be a place of $\mathbb{Q}$ given by a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, write $F = \mathbb{Q}_p$ for the completion `p.adicCompletion ℚ`, equipped with its Borel $\sigma$-algebra `localBorel`. Let $\sigma : \mathrm{Fin}\,2 \to \mathbb{R}$ satisfy $\sigma_1 < \sigma_0$, and let $\Phi : F^2 \to \mathbb{C}$ be locally constant with compact support. Then there exist monoid homomorphisms $\mu_0, \mu_1 : F^\times \to \mathbb{C}^\times$ and a function $f : \mathrm{GL}_2(F) \to \mathbb{C}$ such that: each $\mu_i$ is locally constant; $\mu_i(a) = \lVert a\rVert^{\sigma_i}$ as a complex number, and likewise $\lvert \mu_i(a)\rvert = \lVert a\rVert^{\sigma_i}$, for all $a \in F^\times$; $f$ lies in `principalSeries2 p μa`, i.e. $f$ is locally constant, $f\bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr)g) = f(g)$ for all $x \in F$ and $g$, and $f(\mathrm{diag}(a_0,a_1)g) = \mu_0(a_0)\mu_1(a_1)\sqrt{\lVert a_0\rVert/\lVert a_1\rVert}\,f(g)$ for all $a \in (F^\times)^2$ and $g$; every value $f(g)$ has non-negative real part and vanishing imaginary part; and for every $g \in \mathrm{GL}_2(F)$ the function $t \mapsto \lVert \Phi(t\,e_2 g)\rVert \,\mu_0(t)\mu_1(t)^{-1}\,\mathrm{modulus}(t)$ on $F^\times$ (with $e_2 g$ the second row of $g$) is integrable for the Haar measure on $F^\times$ obtained by pulling back along `Units.val` the multiplicative measure `mulMeasure (selfDualHaarAt ℚ p)`, and $f(g)$ equals $\mu_0(\det g)\,\mathrm{modulus}(\det g)^{1/2}$ times the integral of that function.
--
--   This is the existence of a Godement section attached to $\lvert\Phi\rvert$: a non-negative vector in the principal series $I(\mu_0,\mu_1)$ for the real norm-power characters $\lVert\cdot\rVert^{\sigma_i}$, together with the absolutely convergent zeta-integral formula expressing it, the chamber condition $\sigma_1 < \sigma_0$ guaranteeing convergence at $t \to 0$. It serves as the majorising input for the local Rankin–Selberg convergence statements on products of row integrals and Whittaker functions that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_normPowChar_godementSection_abs_mem_principalSeries2_of_lt.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction
open NumberField.AdelicLevel (diagOne)

theorem LanglandsTunnell.RankinSelberg.exists_normPowChar_godementSection_abs_mem_principalSeries2_of_lt
    (p : HeightOneSpectrum (𝓞 ℚ))
    (σ : Fin 2 → ℝ) (h01 : σ 1 < σ 0)
    (Φ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    letI := localBorel ℚ p
    ∃ (μa : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ i, IsLocallyConstant (μa i)) ∧
      (∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ((μa i a : ℂˣ) : ℂ) = (((‖(a : p.adicCompletion ℚ)‖ ^ (σ i) : ℝ)) : ℂ)) ∧
      (∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μa i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i)) ∧
      f ∈ principalSeries2 p μa ∧
      (∀ g : GL (Fin 2) (p.adicCompletion ℚ), 0 ≤ (f g).re ∧ (f g).im = 0) ∧
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        Integrable (fun t : (p.adicCompletion ℚ)ˣ => (fun v : Fin 2 → p.adicCompletion ℚ => ((‖Φ v‖ : ℝ) : ℂ)) (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) * ((μa 0 t : ℂˣ) : ℂ) * (((μa 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        f g = ((μa 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          ∫ t : (p.adicCompletion ℚ)ˣ, (fun v : Fin 2 → p.adicCompletion ℚ => ((‖Φ v‖ : ℝ) : ℂ)) (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) * ((μa 0 t : ℂˣ) : ℂ) * (((μa 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by sorry
