-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_Supplement_lemma_2_1_v
-- name    : LogConcaveLattice.Lift.Supplement.lemma_2_1_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:34:13.648217+00:00
-- url     : https://prove2.me/theorems/db1dcc5e-b204-4e15-968d-01aad655d7e3
-- title:
--   Lemma 2.1(v) — Hargé's theorem: $\mathbb E\|X\|_K\le\alpha^{-1/2}\,\mathbb E\|G\|_K$ for centred $\alpha$-strongly log-concave $X$
-- statement:
--   Let $\alpha>0$ and let $X$ be a random vector in $\mathbb R^n$ with an $\alpha$-strongly log-concave probability density $f:\mathbb R^n\to(0,\infty)$, that is, $f$ is smooth, strictly positive, and $\nabla^2(-\log f)(x)\succcurlyeq\alpha\,\mathrm{Id}$ for every $x$. Assume $\mathbb E X=0$. Let $G\sim N(0,\mathrm{Id})$ be a standard Gaussian vector in $\mathbb R^n$, and let $K\subseteq\mathbb R^n$ be a convex body (a compact convex set) with $0\in\operatorname{int}(K)$, with Minkowski functional $\|x\|_K=\inf\{r>0:x\in rK\}$. Then $\mathbb E\|X\|_K$ is finite and
--
--   $$\mathbb E\,\|X\|_K\ \le\ \frac1{\sqrt\alpha}\,\mathbb E\,\|G\|_K .$$
--
--   No symmetry of $f$ or of $K$ is assumed. This Gaussian comparison is the step of the proof of Theorem 1.2 (p. 15) that turns the log-concave lattice lift into a covering-radius bound, applied with $\alpha=2\pi/e$.
--
--   **Formalization Note** The density is represented by $f$ itself ($\mathbb E\,g(X)=\int g(x)f(x)\,dx$); $\|x\|_K$ is Mathlib's `gauge K x` and $G$ has law `stdGaussian (V n)`. Integrability of $x\mapsto\|x\|_Kf(x)$ (and of $\|\cdot\|_K$ against the Gaussian) is part of the conclusion, so the bound cannot hold through the Bochner integral's value $0$ on non-integrable functions.
--
--   Differences from the source:
--   - encoding: X has a probability density f : ℝⁿ → (0, ∞) → ∫ f = 1, with smoothness and f > 0 part of IsStronglyLogConcave α f; reason: in Lean ∫ f = 1 forces f to be integrable (a non-integrable function has integral 0), and the published definition of strong log-concavity contains smoothness and positivity; same instances
--   - encoding: E X = 0 → x ↦ f(x)·x is integrable and ∫ f(x)·x dx = 0; reason: the mean exists only for an integrable X; an α-strongly log-concave density has moments of all orders, so no instance is excluded
--   - encoding: K ⊆ ℝⁿ a convex body with 0 ∈ int(K) → K convex and compact with 0 ∈ interior K; reason: a convex body is a compact convex set with nonempty interior, and nonempty interior is implied by 0 ∈ int(K); same instances
--   - encoding: E ‖G‖_K with G ∼ N(0, Id) → ∫ gauge K x ∂(stdGaussian (V n)), the Bochner integral of the Minkowski functional against Mathlib's standard Gaussian measure on EuclideanSpace ℝ (Fin n), with integrability of gauge K against it asserted; reason: stdGaussian is the law N(0, Id); gauge K is continuous and grows linearly for 0 ∈ int K, so the asserted integrability holds in every instance and the integral is the true expectation; the clause guards against the Bochner junk value 0
--   - encoding: E ‖X‖_K ≤ (1/√α) E ‖G‖_K → x ↦ gauge K x · f x is integrable, and ∫ gauge K x · f x ≤ (1/√α) ∫ gauge K ∂γ; reason: the integrability clause guards against the Bochner junk value 0; E ‖X‖_K is finite in every instance because ‖x‖_K ≤ C‖x‖ and X has a finite first moment
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, SHA-256 c2ca89e66a6221772830cc9470a9d1f7fb2afeb8fc716a1b283f35b2280c5eac, Lemma 2.1(v) (Hargé's theorem [13]), p. 6; standing hypotheses of Lemma 2.1 (α > 0, α-strongly log-concave probability density, E X = 0 in (iii)–(v)), p. 6; strong log-concavity p. 3; Minkowski functional p. 4; used in the proof of Theorem 1.2, p. 15

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Definitions.Def_LogConcaveLattice_Lift_StronglyLogConcave

open MeasureTheory ProbabilityTheory

namespace LogConcaveLattice.Lift.Supplement

/-- **Lemma 2.1(v)** (Hargé's theorem; Letwin–Reis–Rothvoss, p. 6). Let `α > 0` and let `X`
have an `α`-strongly log-concave probability density `f : ℝⁿ → (0, ∞)` with `E X = 0`. If
`G ∼ N(0, Id)` and `K ⊆ ℝⁿ` is a convex body with `0 ∈ int K`, then
`E ‖X‖_K ≤ (1/√α) · E ‖G‖_K`, where `‖x‖_K = gauge K x` is the Minkowski functional.
Both expectations `E ‖G‖_K` and `E ‖X‖_K = ∫ ‖x‖_K f(x) dx` are asserted to exist. -/
theorem lemma_2_1_v (n : ℕ) (α : ℝ) (hα : 0 < α) (f : V n → ℝ)
    (hf : IsStronglyLogConcave α f) (hnorm : ∫ x, f x = 1)
    (hmean_int : Integrable (fun x => f x • x)) (hmean : ∫ x, f x • x = 0)
    (K : Set (V n)) (hKconv : Convex ℝ K) (hKcpt : IsCompact K)
    (hK0 : (0 : V n) ∈ interior K) :
    Integrable (fun x => gauge K x) (stdGaussian (V n)) ∧
      Integrable (fun x => gauge K x * f x) ∧
      ∫ x, gauge K x * f x ≤ (1 / Real.sqrt α) * ∫ x, gauge K x ∂(stdGaussian (V n)) := by sorry

end LogConcaveLattice.Lift.Supplement
