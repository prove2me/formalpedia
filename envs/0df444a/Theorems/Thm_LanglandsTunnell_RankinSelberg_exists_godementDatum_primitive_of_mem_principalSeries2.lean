-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2
-- name    : LanglandsTunnell.RankinSelberg.exists_godementDatum_primitive_of_mem_principalSeries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/2877813b-3955-5514-8a86-928afe00b9c8
-- title:
--   Principal series vectors as Godement sections on primitive vectors
-- statement:
--   Let $p$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, write $F = \mathbb{Q}_p$ for the $p$-adic completion, let $\mu_0,\mu_1 \colon F^\times \to \mathbb{C}^\times$ be monoid homomorphisms (no continuity or unitarity assumed), and let $\varphi \colon \mathrm{GL}_2(F) \to \mathbb{C}$ lie in `principalSeries2`, i.e. $\varphi$ is locally constant, satisfies $\varphi\bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr)g) = \varphi(g)$ for all $x \in F$, and $\varphi(\mathrm{diag}(a_0,a_1)g) = \mu_0(a_0)\mu_1(a_1)\sqrt{\lVert a_0\rVert/\lVert a_1\rVert}\,\varphi(g)$ for all $a_0,a_1 \in F^\times$. Then, with $F$ carrying its Borel structure, there is a locally constant, compactly supported $\Phi_1 \colon F^2 \to \mathbb{C}$ vanishing off the primitive vectors, in the sense that $\Phi_1(v) \neq 0$ forces $|v_j| \le 1$ for both coordinates and $|v_j| = 1$ for at least one, such that for every $g \in \mathrm{GL}_2(F)$ the function $t \mapsto \Phi_1(t\,e_2 g)\,\mu_0(t)\mu_1(t)^{-1}\,\mathrm{modulus}(t)$, where $e_2 g$ is the second row of $g$ and $\mathrm{modulus}(t) = \lVert t\rVert$, is integrable for the measure on $F^\times$ obtained by pulling back along $F^\times \hookrightarrow F$ the measure with density $\mathrm{modulus}^{-1}$ relative to the self-dual additive Haar measure `selfDualHaarAt`, and $$\varphi(g) = \mu_0(\det g)\,\lVert \det g\rVert^{1/2} \int_{F^\times} \Phi_1(t\,e_2 g)\,\mu_0(t)\mu_1(t)^{-1}\,\lVert t\rVert\,d^\times t.$$
--
--   This is the local statement that a vector in the (normalised) principal series of $\mathrm{GL}_2(\mathbb{Q}_p)$ is the Godement section attached to a Schwartz–Bruhat function on $\mathbb{Q}_p^2$ which may moreover be taken to be supported on the primitive vectors. It supplies the input for the Godement-section hypothesis used in the local Rankin–Selberg computations at principal-series places, both in the Borel-eigenfunctional and in the cuspidal case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_godementDatum_primitive_of_mem_principalSeries2.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_godementDatum_primitive_of_mem_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ) :
    letI := localBorel ℚ p
    ∃ Φ₁ : (Fin 2 → p.adicCompletion ℚ) → ℂ, IsLocallyConstant Φ₁ ∧ HasCompactSupport Φ₁ ∧
      (∀ v : Fin 2 → p.adicCompletion ℚ, Φ₁ v ≠ 0 →
        (∀ j : Fin 2, Valued.v (v j) ≤ 1) ∧ ∃ j : Fin 2, Valued.v (v j) = 1) ∧
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        Integrable (fun t : (p.adicCompletion ℚ)ˣ => Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) * ((μ 0 t : ℂˣ) : ℂ) * (((μ 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        φ g = ((μ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          ∫ t : (p.adicCompletion ℚ)ˣ, Φ₁ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) * ((μ 0 t : ℂˣ) : ℂ) * (((μ 1 t : ℂˣ) : ℂ))⁻¹ * ((modulus (t : p.adicCompletion ℚ) : ℝ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by sorry
