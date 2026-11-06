-- Prove2me | Theorems.Thm_GeomDRSub_lemma_5_2
-- name    : GeomDRSub.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:11:49.092338+00:00
-- url     : https://prove2.me/theorems/e4e05f8b-4c42-4e00-bbb3-86171b53dd93
-- title:
--   Lemma 5.2 — OMBQ with projected ascent
-- statement:
--   Let $K\subseteq\mathbb R^d$ be nonempty, compact and convex, $D\ge\operatorname{diam}K$, and let $f_1,\dots,f_T$ be fixed (oblivious adversary). On round $t$ an algorithm commits $p_t\in K$, computes $\hat g_t\in\mathbb R^d$ and updates $x_{t+1}=\Pi_K(x_t+\eta\hat g_t)$ from $x_1\in K$. Let $F_t$ contain all random choices and responses before round $t$ (so $x_t$ is $F_t$-measurable). Suppose $\alpha\in[0,1]$, $\beta>0$, $V\ge0$ and deterministic $\mathrm{err}_1,\dots,\mathrm{err}_T$ satisfy, for every $t$ and every $o\in K$,
--   $$
--   \alpha f_t(o)-\mathbb E[f_t(p_t)\mid F_t]\le\beta\,\mathbb E[\langle\hat g_t,o-x_t\rangle\mid F_t]+\mathrm{err}_t,\qquad\mathbb E[\|\hat g_t\|_2^2\mid F_t]\le V .
--   $$
--   1. If $D>0$, $V>0$ and $\eta=D/\sqrt{VT}$, then for every $o\in K$
--   $$
--   \alpha\sum_{t=1}^Tf_t(o)-\mathbb E\sum_{t=1}^Tf_t(p_t)\le\beta D\sqrt{VT}+\sum_{t=1}^T\mathrm{err}_t ;
--   $$
--   if $D=0$ or $V=0$, the same bound holds with the state held fixed at $x_1$ ($\eta=0$).
--   2. Let $H$ be a randomized action (a Markov kernel) and $g$ a field such that $g(f_t,x_t)$ is $F_t$-measurable and $\alpha f_t(o)-\mathbb E[f_t(H(x_t))\mid x_t]\le\beta\langle g(f_t,x_t),o-x_t\rangle$ for every $o\in K$. If $\hat g_t$ is conditionally unbiased for $g(f_t,x_t)$ given $F_t$ and $p_t$ is drawn from the law of $H(x_t)$ given $F_t$, then the first condition above holds with $\mathrm{err}_t=0$.
--
--   This is the online reduction: an upper-linearizable comparison and a field estimate with bounded second moment yield $O(\sqrt T)$ regret.
--
--   Differences from the source:
--   - generalization: K the standing nonempty compact convex down-closed subset of [0,1]^d → K nonempty, compact, convex; reason: down-closedness and K ⊆ [0,1]^d are not used; specializes to the standing K
--   - generalization: the paper's objectives (nonnegative, C¹, DR-submodular) → arbitrary real functions f_t with f_t(p_t) integrable; reason: Lemma 5.2 uses no property of the objectives; specializes
--   - reading: p_t drawn from the law of H(x_t) independently of F_t given x_t → the conditional law of p_t given F_t is H(x_t); reason: this is the consequence the paper's proof uses ("p_t has the law of H(x_t) given F_t")
--   - encoding: F_t contains all random choices and responses before round t → a filtration F with ĝ_t F_{t+1}-measurable, each F t a sub-σ-algebra; reason: makes x_t F_t-measurable as on the page
--   - encoding: Reg_α(T) = α max_{o∈K} Σ f_t(o) − E Σ f_t(p_t) → the bound for every o ∈ K; reason: the same bound for the maximizer, without assuming it is attained
--   - encoding: η = D/√(VT) if D, V > 0; state fixed at x₁ if D = 0 or V = 0 → η = stepSize D V T; reason: stepSize is D/√(TV) or 0, and step 0 holds the state fixed
--   - encoding: conditional expectations of f_t(p_t), ĝ_t, ‖ĝ_t‖²; E[f_t(H(x_t)) | x_t] → integrability of f_t(p_t), ĝ_t, ‖ĝ_t‖²; p_t measurable; f_t measurable and integrable for H(y), y ∈ K; reason: presupposed by the expectations; rules out Lean's junk value 0; only the values of f_t on the support of the actions matter, so measurability on all of ℝ^d excludes no instance
--   - encoding: randomized action H, field g(f_t, ·), and (63) with E[f_t(H(x_t)) | x_t] → Markov kernel H on ℝ^d and a map g t on ℝ^d, both chosen per round, and (63) almost surely for each o ∈ K with ∫ f_t dH(x_t); reason: the kernel's integral is a version of the conditional expectation, which is defined almost surely
--   - encoding: x₁ ∈ K → x 0 ω = x₁ for every ω, x₁ ∈ K, rounds 0-based; reason: x₁ is the deterministic initial state
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Lemma 5.2, pp.19–20, Eqs. (61)–(63)

import Mathlib
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj
import Definitions.Def_GeomDRSub_stepSize

namespace GeomDRSub

open MeasureTheory ProbabilityTheory

/-- **Lemma 5.2 (OMBQ with projected ascent).** Aggarwal–Lu, arXiv:2610.00545, pp.19–20: "Let
`f₁, …, f_T` be chosen by an oblivious adversary, and let `D ≥ diam(K)`. On round `t` the algorithm
commits an action `p_t ∈ K`, then computes a vector `ĝ_t ∈ ℝᵈ`, and updates
`x_{t+1} = Π_K(x_t + ηĝ_t)` from `x₁ ∈ K`. Let `F_t` contain the objective sequence and all random
choices and responses before round `t`, so that `x_t` is `F_t`-measurable. Suppose that
`α ∈ [0, 1]`, `β > 0`, `V ≥ 0`, and deterministic numbers `err₁, …, err_T` satisfy, for every `t`
and every `o ∈ K`,
`αf_t(o) − E[f_t(p_t) | F_t] ≤ β E[⟨ĝ_t, o − x_t⟩ | F_t] + err_t`, `E[‖ĝ_t‖₂² | F_t] ≤ V`. (61)
If `D > 0`, `V > 0`, and `η = D/√(VT)`, then `Reg_α(T) ≤ βD√(VT) + ∑_{t=1}^T err_t`. (62)
If `D = 0` or `V = 0`, then (62) holds with the state held fixed at `x₁`. Moreover, let `H` be a
randomized action and `g` a field such that `g(f_t, x_t)` is `F_t`-measurable and, for every
`o ∈ K`, `αf_t(o) − E[f_t(H(x_t)) | x_t] ≤ β⟨g(f_t, x_t), o − x_t⟩`. (63) If `ĝ_t` is
conditionally unbiased for `g(f_t, x_t)` given `F_t` and `p_t` is drawn from the law of `H(x_t)`
independently of `F_t` given `x_t`, then the first condition in (61) holds with `err_t = 0`."

Conjuncts:
1. under (61), for every `o ∈ K`, `α ∑ f_t(o) − E ∑ f_t(p_t) ≤ βD√(VT) + ∑ err_t`, with the step
   `η = stepSize D V T` (which is `D/√(VT)` if `D, V > 0` and `0`, the fixed state, otherwise);
2. the "Moreover" clause, for every round `t < T`.

**Formalization Note.** Rounds are 0-based. `F` is any filtration of sub-σ-algebras; "`F_{t+1}`
contains the choices and responses of round `t`" is `ĝ_t` being `F_{t+1}`-measurable (so `x_t` is
`F_t`-measurable). `x₁` is a fixed point of `K`. `K` is nonempty, compact and convex (the
down-closedness and `K ⊆ [0,1]^d` of the standing assumptions are not needed). The objectives are
arbitrary real functions; integrability of `f_t(p_t)`, `ĝ_t` and `‖ĝ_t‖²` is assumed so that the
conditional expectations of (61) are not Lean's junk value `0`. Regret is stated for every
comparator `o ∈ K` (equal to the maximum for compact `K` and continuous objectives). The randomized
action `H` is a Markov kernel; "`p_t` is drawn from the law of `H(x_t)` independently of `F_t` given
`x_t`" is that the conditional law of `p_t` given `F_t` is `H(x_t)`. The expectation in (63)
requires `f_t` measurable and integrable for `H(x)`, `x ∈ K`, and (63), an inequality with a
conditional expectation, is assumed almost surely for each `o ∈ K`. -/
theorem lemma_5_2 {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKne : K.Nonempty) (hKc : IsCompact K)
    (hKcv : Convex ℝ K) (D : ℝ) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D)
    (T : ℕ) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (F : ℕ → MeasurableSpace Ω) (hFmono : Monotone F) (hFle : ∀ t, F t ≤ mΩ)
    (p ĝ x : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (x₁ : EuclideanSpace ℝ (Fin d)) (hx₁ : x₁ ∈ K)
    (hx0 : ∀ ω, x 0 ω = x₁)
    (hĝmeas : ∀ t < T, StronglyMeasurable[F (t + 1)] (ĝ t))
    (hpK : ∀ t < T, ∀ ω, p t ω ∈ K)
    (hfp : ∀ t < T, Integrable (fun ω => f t (p t ω)) P)
    (hĝint : ∀ t < T, Integrable (ĝ t) P)
    (hĝsq : ∀ t < T, Integrable (fun ω => ‖ĝ t ω‖ ^ 2) P)
    (α β V : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : 0 < β) (hV : 0 ≤ V)
    (hupd : ∀ t < T, ∀ ω,
      OrabonaOL.OGD.IsEuclideanProj K (x t ω + stepSize D V T • ĝ t ω) (x (t + 1) ω)) :
    -- (61) ⟹ (62), including the degenerate case D = 0 or V = 0
    (∀ err : ℕ → ℝ,
      (∀ t < T, ∀ o ∈ K, ∀ᵐ ω ∂P,
        α * f t o - P[fun ω => f t (p t ω) | F t] ω ≤
          β * P[fun ω => inner ℝ (ĝ t ω) (o - x t ω) | F t] ω + err t) →
      (∀ t < T, P[fun ω => ‖ĝ t ω‖ ^ 2 | F t] ≤ᵐ[P] fun _ => V) →
      ∀ o ∈ K, α * ∑ t ∈ Finset.range T, f t o - ∫ ω, ∑ t ∈ Finset.range T, f t (p t ω) ∂P ≤
        β * D * Real.sqrt (V * T) + ∑ t ∈ Finset.range T, err t) ∧
    -- the "Moreover" clause: (63) gives the first condition of (61) with err_t = 0
    (∀ t < T, ∀ (H : Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
        (g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      IsMarkovKernel H → Measurable (f t) → Measurable (p t) →
      (∀ y ∈ K, Integrable (f t) (H y)) →
      StronglyMeasurable[F t] (fun ω => g t (x t ω)) →
      (∀ o ∈ K, ∀ᵐ ω ∂P, α * f t o - ∫ y, f t y ∂(H (x t ω)) ≤
        β * inner ℝ (g t (x t ω)) (o - x t ω)) →
      P[ĝ t | F t] =ᵐ[P] (fun ω => g t (x t ω)) →
      (∀ A : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet A →
        P[(p t ⁻¹' A).indicator (fun _ => (1 : ℝ)) | F t] =ᵐ[P]
          fun ω => (H (x t ω) A).toReal) →
      ∀ o ∈ K, ∀ᵐ ω ∂P,
        α * f t o - P[fun ω => f t (p t ω) | F t] ω ≤
          β * P[fun ω => inner ℝ (ĝ t ω) (o - x t ω) | F t] ω + 0) := by sorry

end GeomDRSub
