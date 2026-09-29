-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_MellinUniqueness_eq_of_forall_continuous_char_exists_laplace_eq
-- name    : LanglandsTunnell.Converse.MellinUniqueness.eq_of_forall_continuous_char_exists_laplace_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/16c77dad-b1fc-5cca-97b6-957484a98d4d
-- title:
--   Character-twisted Laplace uniqueness on C × ℝ
-- statement:
--   Let $C$ be a group equipped with a compact topology, its Borel $\sigma$-algebra, and a Haar measure $\mu$ (left invariant, finite on compacts, positive on non-empty open sets). Assume the continuous characters separate the identity: for every $x \in C$ with $x \neq 1$ there is a continuous monoid homomorphism $\chi : C \to \mathbb{C}^{\times}$ with $\chi(x) \neq 1$. Let $f_1, f_2 : C \times \mathbb{R} \to \mathbb{C}$ be continuous, and let $\Lambda$ assign to each monoid homomorphism $\chi : C \to \mathbb{C}^{\times}$ a function $\Lambda_\chi : \mathbb{C} \to \mathbb{C}$ such that, for every continuous $\chi$, $\Lambda_\chi$ is differentiable on all of $\mathbb{C}$ and bounded on every vertical strip, in the sense that for all real $a \le b$ there is a constant bounding $\|\Lambda_\chi(s)\|$ for all $s$ with $a \le \operatorname{Re} s \le b$. Assume finally that for every continuous $\chi$ there exists $c \in \mathbb{R}$ such that: for all $s$ with $\operatorname{Re} s > c$ the function $(x,t) \mapsto f_1(x,t)\,\chi(x)\,e^{st}$ is integrable for $\mu \otimes dt$ with integral $\Lambda_\chi(s)$, and for all $s$ with $\operatorname{Re} s < -c$ the function $(x,t) \mapsto f_2(x,t)\,\chi(x)\,e^{st}$ is integrable for $\mu \otimes dt$ with integral $\Lambda_\chi(s)$. Then $f_1 = f_2$.
--
--   This is the uniqueness step of the converse-theorem argument in the style of Jacquet–Langlands Lemma 11.3.1: a pair of functions on a compact group times the real line whose character-twisted Laplace transforms share one entire, strip-bounded continuation must coincide, the abscissa of convergence being allowed to depend on the character. It reduces, character by character, to the one-variable statement [`LanglandsTunnell.Converse.MellinUniqueness.eq_of_laplace_eq_of_boundedOnStrips`](thm.html#LanglandsTunnell.Converse.MellinUniqueness.eq_of_laplace_eq_of_boundedOnStrips), and is used in the cusp-synthesis step [`LanglandsTunnell.Converse.CuspSynthesis.jlSeries_globalPoints_mul_eq_of_isJLNice`](thm.html#LanglandsTunnell.Converse.CuspSynthesis.jlSeries_globalPoints_mul_eq_of_isJLNice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_MellinUniqueness_eq_of_forall_continuous_char_exists_laplace_eq.lean

import Definitions.Def_LanglandsTunnell_HonestLDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory

theorem LanglandsTunnell.Converse.MellinUniqueness.eq_of_forall_continuous_char_exists_laplace_eq
    (C : Type) [Group C] [TopologicalSpace C] [CompactSpace C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure]
    (hsep : ∀ x : C, x ≠ 1 → ∃ χ : C →* ℂˣ, Continuous χ ∧ χ x ≠ 1)
    (f₁ f₂ : C × ℝ → ℂ) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (Λ : (C →* ℂˣ) → ℂ → ℂ)
    (hΛ : ∀ χ : C →* ℂˣ, Continuous χ → Differentiable ℂ (Λ χ))
    (hb : ∀ χ : C →* ℂˣ, Continuous χ → LDatum.BoundedOnStrips (Λ χ))
    (h : ∀ χ : C →* ℂˣ, Continuous χ → ∃ c : ℝ,
      (∀ s : ℂ, c < s.re →
        Integrable (fun p : C × ℝ => f₁ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ))) (μ.prod volume) ∧
          ∫ p : C × ℝ, f₁ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ s) ∧
      (∀ s : ℂ, s.re < -c →
        Integrable (fun p : C × ℝ => f₂ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ))) (μ.prod volume) ∧
          ∫ p : C × ℝ, f₂ p * ((χ p.1 : ℂˣ) : ℂ) * Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ s)) :
    f₁ = f₂ := by sorry
