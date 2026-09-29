-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window
-- name    : LanglandsTunnell.TateLocal.integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/648be50b-27b1-5afb-969f-21e2c6012fc9
-- title:
--   Multiplicative Fourier inversion at a finite place of ℚ
-- statement:
--   Fix a height-one prime $p$ of the ring of integers of $\mathbb{Q}$ and write $F = \mathbb{Q}_p$ for the $p$-adic completion, $\psi =$ `psiLocal` $\mathbb{Q}\,p$ for the restriction to $F$ of the standard adelic additive character along the additive embedding of $F$ into the adele ring, and $dy$ for `selfDualHaarAt` $\mathbb{Q}\,p$, the additive Haar measure giving the valuation ring the mass $(\mathrm{absNorm}\,p)^{-\mathrm{addCharLevel}(\psi)/2}$, the completion carrying its Borel $\sigma$-algebra. Let $Fn \colon F^\times \to \mathbb{C}$, let $n_1, n_0$ be integers and $m$ a natural number, and assume: $Fn\,y = 0$ whenever $\exp(-n_1) < v(y)$ or $v(y) < \exp(-n_0)$; and $Fn(yu) = Fn\,y$ for all units $y, u$ with $v(u) = 1$ and $v(u-1) \le \exp(-m)$. Let $b \in F^\times$. Denote by $d^\times t$ the measure on $F^\times$ obtained as the comap along $t \mapsto t$ of `mulMeasure` $dy$, i.e. of $dy$ restricted to $F \setminus \{0\}$ with density $\mathrm{modulus}(x)^{-1}$, where $\mathrm{modulus}(x)$ is the module of multiplication by $x$ for $dy$. Then three assertions hold: the function $y \mapsto \int_{F^\times} Fn(t)\,\psi(ty)\,d^\times t$ is integrable for $dy$; $\int_F \bigl(\int_{F^\times} Fn(t)\psi(ty)\,d^\times t\bigr)\psi(by)\,dy = \mathrm{modulus}(b)^{-1} Fn(-b)$; and the same identity with $\psi(ty)$ and $\psi(by)$ replaced by $\psi(-ty)$ and $\psi(-by)$.
--
--   This is Fourier inversion for the self-dual measure on $\mathbb{Q}_p$, written multiplicatively: the inner integral is the Fourier transform of the Schwartz–Bruhat function $t \mapsto Fn(t)/|t|$ extended by $0$ at the origin, whose local constancy and compact support come from the two hypotheses (support in a finite window of valuation shells, invariance under the units congruent to $1$ modulo $p^m$), and the two sign variants record the inversion formula for $\psi$ and for $\bar\psi$. It feeds the computation of Fourier coefficients of Kirillov-model functions in the Rankin–Selberg part of the development, through [`LanglandsTunnell.RankinSelberg.matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal`](thm.html#LanglandsTunnell.RankinSelberg.matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.integrable_unitsFourier_and_integral_mul_psiLocal_eq_inv_modulus_mul_of_shell_window
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Fn : (p.adicCompletion ℚ)ˣ → ℂ) (n₁ n₀ : ℤ) (m : ℕ)
    (hf₀ : ∀ y : (p.adicCompletion ℚ)ˣ,
      WithZero.exp (-n₁) < Valued.v (y : p.adicCompletion ℚ) ∨ Valued.v (y : p.adicCompletion ℚ) < WithZero.exp (-n₀) →
        Fn y = 0)
    (hf₁ : ∀ y u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(m : ℤ)) → Fn (y * u) = Fn y)
    (b : (p.adicCompletion ℚ)ˣ) :
    letI := localBorel ℚ p
    Integrable (fun y : p.adicCompletion ℚ =>
        ∫ t : (p.adicCompletion ℚ)ˣ, Fn t * NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ) * y)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) (selfDualHaarAt ℚ p) ∧
    (∫ y : p.adicCompletion ℚ,
        (∫ t : (p.adicCompletion ℚ)ˣ, Fn t * NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ) * y)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
        NumberField.StandardAddChar.psiLocal ℚ p ((b : p.adicCompletion ℚ) * y) ∂(selfDualHaarAt ℚ p)) =
      (((modulus (b : p.adicCompletion ℚ) : ℝ) : ℂ))⁻¹ * Fn (-b) ∧
    (∫ y : p.adicCompletion ℚ,
        (∫ t : (p.adicCompletion ℚ)ˣ, Fn t * NumberField.StandardAddChar.psiLocal ℚ p (-((t : p.adicCompletion ℚ) * y))
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) *
        NumberField.StandardAddChar.psiLocal ℚ p (-((b : p.adicCompletion ℚ) * y)) ∂(selfDualHaarAt ℚ p)) =
      (((modulus (b : p.adicCompletion ℚ) : ℝ) : ℂ))⁻¹ * Fn (-b) := by sorry
