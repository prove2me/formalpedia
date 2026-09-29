-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
-- name    : LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/696e37ad-dd49-5e73-a9c0-6b82c159dc92
-- title:
--   Shell calculus for the multiplicative Haar measure on ℚₚ^×
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, and equip the completion $\mathbb{Q}_p =$ `p.adicCompletion ℚ` with its Borel $\sigma$-algebra (`localBorel`). Write $\mu$ for `selfDualHaarAt ℚ p`, the additive Haar measure normalising the valuation subring of $\mathbb{Q}_p$ to mass $1$ and then scaled by $N(p)^{-n(\psi)/2}$, where $N(p)$ is the absolute norm of the prime ideal and $n(\psi)$ is the level $\sup\{n : \psi(x)=1 \text{ whenever } v(x)\le \exp n\}$ of the local component $\psi$ of the standard additive character; write $\mu^{\times}$ for the pullback along $y\mapsto y$ of the measure $(\mathrm{mod}\,x)^{-1}\,d\mu(x)$ on $\mathbb{Q}_p\setminus\{0\}$, the module $\mathrm{mod}$ being the distributive Haar character. For $n\in\mathbb{Z}$ let $S_n=\{y\in\mathbb{Q}_p^{\times} : v(y)=\exp(-n)\}$. The theorem asserts the conjunction of: (i) each $S_n$ is measurable; (ii) each $y\in\mathbb{Q}_p^{\times}$ lies in $S_n$ for exactly one $n$; (iii) for each $n$, $\mu^{\times}(S_n)=\mu^{\times}(S_0)$ and $0<\mu^{\times}(S_n)<\infty$; (iv) if $y\in S_n$ then $\mathrm{mod}(y)=N(p)^{-n}$ as a real number; and (v) for every $f:\mathbb{Q}_p^{\times}\to\mathbb{C}$ which is $\mu^{\times}$-integrable, the family $n\mapsto\int_{S_n}f\,d\mu^{\times}$ has sum $\int f\,d\mu^{\times}$.
--
--   This is the shell calculus of Tate's thesis for the multiplicative Haar measure $d^{\times}y=dy/|y|$ on the local field at $p$: the shells partition the units, all have the same finite positive mass, the module is constant on each shell, and integrals may be computed shell by shell. It is the form in which shell-by-shell manipulations of local zeta integrals and of torus integrals are carried out downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel

theorem
  LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    (∀ n : ℤ, MeasurableSet {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))}) ∧
    (∀ y : (p.adicCompletion ℚ)ˣ,
      ∃! n : ℤ, y ∈ {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))}) ∧
    (∀ n : ℤ,
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} =
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-((0 : ℤ)))} ∧
      0 < (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} ∧
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
          {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} < ⊤) ∧
    (∀ (n : ℤ) (y : (p.adicCompletion ℚ)ˣ),
      y ∈ {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))} →
      (modulus (y : p.adicCompletion ℚ) : ℝ) = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-n)) ∧
    (∀ f : (p.adicCompletion ℚ)ˣ → ℂ, Integrable f (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) →
      HasSum
        (fun n : ℤ =>
          ∫ y in {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n))}, f y
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
        (∫ y, f y ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))) := by sorry
