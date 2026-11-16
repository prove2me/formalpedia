-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_Supplement_lemma_2_1_iii
-- name    : LogConcaveLattice.Lift.Supplement.lemma_2_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:35:31.466982+00:00
-- url     : https://prove2.me/theorems/ce4972e3-1c0d-4d21-bf87-5783e2d43aca
-- title:
--   Lemma 2.1(iii) — a centred $\alpha$-strongly log-concave vector is $\alpha^{-1/2}$-subgaussian: $\mathbb E e^{\langle X,u\rangle}\le e^{\|u\|^2/(2\alpha)}$
-- statement:
--   Let $\alpha>0$ and let $X$ be a random vector in $\mathbb R^n$ with an $\alpha$-strongly log-concave probability density $f:\mathbb R^n\to(0,\infty)$ (smooth, strictly positive, $\nabla^2(-\log f)\succcurlyeq\alpha\,\mathrm{Id}$ everywhere), and assume $\mathbb E X=0$. Then $X$ is $\alpha^{-1/2}$-subgaussian: for every $u\in\mathbb R^n$ the moment generating function $\mathbb E\,e^{\langle X,u\rangle}$ is finite and
--
--   $$\mathbb E\,e^{\langle X,u\rangle}\ \le\ e^{\|u\|_2^2/(2\alpha)} .$$
--
--   This is the subgaussian estimate used twice (for $X$ and for $Z$) in the Cauchy–Schwarz step of the proof of Theorem 4.2 (p. 18), with $\alpha=2\pi/e$.
--
--   **Formalization Note** The density is represented by $f$ itself, $\mathbb E\,e^{\langle X,u\rangle}=\int e^{\langle x,u\rangle}f(x)\,dx$. Integrability of $x\mapsto e^{\langle x,u\rangle}f(x)$ is part of the conclusion, so the bound cannot hold through the Bochner integral's value $0$ on non-integrable functions.
--
--   Differences from the source:
--   - encoding: X has a probability density f : ℝⁿ → (0, ∞) → ∫ f = 1, with smoothness and f > 0 part of IsStronglyLogConcave α f; reason: in Lean ∫ f = 1 forces f to be integrable (a non-integrable function has integral 0), and the published definition of strong log-concavity contains smoothness and positivity; same instances
--   - encoding: E X = 0 → x ↦ f(x)·x is integrable and ∫ f(x)·x dx = 0; reason: the mean exists only for an integrable X; an α-strongly log-concave density has moments of all orders, so no instance is excluded
--   - encoding: E e^{⟨X,u⟩} ≤ e^{∥u∥²/(2α)} → x ↦ exp⟨x,u⟩ · f x is integrable, and ∫ exp⟨x,u⟩ · f x ≤ exp(‖u‖²/(2α)); reason: the integrability clause guards against the Bochner junk value 0; the source's bound asserts finiteness, so no instance changes
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, SHA-256 c2ca89e66a6221772830cc9470a9d1f7fb2afeb8fc716a1b283f35b2280c5eac, Lemma 2.1(iii) (Subgaussianity, [1, Eq. (5.4.1)]), p. 6; standing hypotheses of Lemma 2.1, p. 6; s-subgaussian p. 4; used in the proof of Theorem 4.2, p. 18

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Definitions.Def_LogConcaveLattice_Lift_StronglyLogConcave

open MeasureTheory
open scoped RealInnerProductSpace

namespace LogConcaveLattice.Lift.Supplement

/-- **Lemma 2.1(iii)** (subgaussianity; Letwin–Reis–Rothvoss, p. 6). Let `α > 0` and let `X`
have an `α`-strongly log-concave probability density `f : ℝⁿ → (0, ∞)` with `E X = 0`. Then
`X` is `α^{-1/2}`-subgaussian: for every `u ∈ ℝⁿ`, `E e^{⟨X,u⟩} ≤ e^{‖u‖²/(2α)}`.
The expectation `E e^{⟨X,u⟩} = ∫ e^{⟨x,u⟩} f(x) dx` is asserted to be finite. -/
theorem lemma_2_1_iii (n : ℕ) (α : ℝ) (hα : 0 < α) (f : V n → ℝ)
    (hf : IsStronglyLogConcave α f) (hnorm : ∫ x, f x = 1)
    (hmean_int : Integrable (fun x => f x • x)) (hmean : ∫ x, f x • x = 0) :
    ∀ u : V n, Integrable (fun x => Real.exp ⟪x, u⟫ * f x) ∧
      ∫ x, Real.exp ⟪x, u⟫ * f x ≤ Real.exp (‖u‖ ^ 2 / (2 * α)) := by sorry

end LogConcaveLattice.Lift.Supplement
