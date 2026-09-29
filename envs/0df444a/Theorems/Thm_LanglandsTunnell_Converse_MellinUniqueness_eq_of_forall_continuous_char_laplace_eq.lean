-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_MellinUniqueness_eq_of_forall_continuous_char_laplace_eq
-- name    : LanglandsTunnell.Converse.MellinUniqueness.eq_of_forall_continuous_char_laplace_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/2b0435aa-174d-5474-b9b3-fafb0d30499e
-- title:
--   Character-twisted Laplace uniqueness on a compact group times ℝ
-- statement:
--   Let $C$ be a type carrying a group structure and a compact topology (continuity of the multiplication is not assumed), equipped with a measurable space structure that is the Borel structure of the topology, and let $\mu$ be a Haar measure on $C$. Assume the separation hypothesis `hsep`: for every $x \in C$ with $x \neq 1$ there is a monoid homomorphism $\chi : C \to \mathbb{C}^{\times}$ which is continuous and satisfies $\chi(x) \neq 1$. Let $f_1, f_2 : C \times \mathbb{R} \to \mathbb{C}$ be continuous, let $c \in \mathbb{R}$, and let $\Lambda$ assign to each homomorphism $\chi : C \to \mathbb{C}^{\times}$ a function $\Lambda_\chi : \mathbb{C} \to \mathbb{C}$ such that for every continuous $\chi$ the function $\Lambda_\chi$ is differentiable on all of $\mathbb{C}$ and satisfies `LDatum.BoundedOnStrips`, i.e. for all reals $a \le b$ there is a constant $C$ with $\|\Lambda_\chi(s)\| \le C$ whenever $a \le \operatorname{Re} s \le b$. Assume further that for every continuous $\chi$ and every $s$ with $\operatorname{Re} s > c$ the function $(x,t) \mapsto f_1(x,t)\,\chi(x)\,e^{st}$ is integrable for the product of $\mu$ with Lebesgue measure on $\mathbb{R}$ and its integral over $C \times \mathbb{R}$ equals $\Lambda_\chi(s)$; and that for every continuous $\chi$ and every $s$ with $\operatorname{Re} s < -c$ the function $(x,t) \mapsto f_2(x,t)\,\chi(x)\,e^{st}$ is likewise integrable with integral $\Lambda_\chi(s)$. The conclusion is that $f_1 = f_2$ as functions on $C \times \mathbb{R}$.
--
--   This is the uniqueness principle underlying converse theorems for $\mathrm{GL}(2)$, in the shape used by Jacquet and Langlands: a single strip-bounded entire continuation, one for each character twist, determines the function whose two Laplace transforms it represents on the two half-planes. Compared with the textbook version the group here is an abstract group with a compact topology and a Haar measure, subject only to the hypothesis that continuous characters into $\mathbb{C}^{\times}$ separate points from the identity, and $\Lambda$ is allowed to be arbitrary on discontinuous homomorphisms. It feeds the idelic uniqueness statement [`LanglandsTunnell.Converse.MellinUniqueness.eq_smul_of_forall_isAdmissibleTwist_mellin_eq`](thm.html#LanglandsTunnell.Converse.MellinUniqueness.eq_smul_of_forall_isAdmissibleTwist_mellin_eq) for the idele class group of $\mathbb{Q}$, and through it the construction of arithmetic genuine cuspidal realisations from a nice $L$-datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_MellinUniqueness_eq_of_forall_continuous_char_laplace_eq.lean

import Definitions.Def_LanglandsTunnell_HonestLDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory

theorem LanglandsTunnell.Converse.MellinUniqueness.eq_of_forall_continuous_char_laplace_eq
    (C : Type) [Group C] [TopologicalSpace C] [CompactSpace C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure]
    (hsep : ∀ x : C, x ≠ 1 → ∃ χ : C →* ℂˣ, Continuous χ ∧ χ x ≠ 1)
    (f₁ f₂ : C × ℝ → ℂ) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (c : ℝ)
    (Λ : (C →* ℂˣ) → ℂ → ℂ)
    (hΛ : ∀ χ : C →* ℂˣ, Continuous χ → Differentiable ℂ (Λ χ))
    (hb : ∀ χ : C →* ℂˣ, Continuous χ → LDatum.BoundedOnStrips (Λ χ))
    (h₁ : ∀ χ : C →* ℂˣ, Continuous χ → ∀ s : ℂ, c < s.re →
      Integrable (fun p : C × ℝ => f₁ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ))) (μ.prod volume) ∧
        ∫ p : C × ℝ, f₁ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ s)
    (h₂ : ∀ χ : C →* ℂˣ, Continuous χ → ∀ s : ℂ, s.re < -c →
      Integrable (fun p : C × ℝ => f₂ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ))) (μ.prod volume) ∧
        ∫ p : C × ℝ, f₂ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ s) :
    f₁ = f₂ := by sorry
