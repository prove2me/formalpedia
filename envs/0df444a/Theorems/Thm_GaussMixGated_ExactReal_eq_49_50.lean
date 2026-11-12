-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_eq_49_50
-- name    : GaussMixGated.ExactReal.eq_49_50
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:27:04.159374+00:00
-- url     : https://prove2.me/theorems/b57cdc22-fc16-4cd1-9614-0e4c1bc073db
-- title:
--   §8.2, displays (49)–(50) — the regular subset
-- statement:
--   For every $\alpha\in(0,1)$ there are $C,K>0$ such that the following holds. Let $d\ge1$, $B\ge0$, $0<\tau<1$, and let $D$ be a probability measure on $\mathbb R^d$ with finite second moments, mean $m$ and $\operatorname{Cov}(D)\preceq B^2I_d$. If
--
--   $$n\ge C\,[d\log(2d)+\log(1/\tau)],\qquad(49)$$
--
--   then an i.i.d. sample $x_1,\dots,x_n$ from $D$ contains, with probability at least $1-\tau/2$, a set $G$ of at least $(1-\alpha/2)n$ indices with
--
--   $$\frac1n\sum_{i\in G}(x_i-m)(x_i-m)^{\top}\preceq KB^2I_d.\qquad(50)$$
--
--   This is the consequence of the regular-subset theorem of Diakonikolas, Kane and Pensia [DKP21, Theorem 1.4] that the posterior cover uses; the normalization is $1/n$, not $1/|G|$.
--
--   Differences from the source:
--   - reading: for a fixed sufficiently small α > 0 there are universal C, K → for every α ∈ (0, 1) there are C, K > 0; reason: read "a fixed sufficiently small α" as any fixed sufficiently small positive α; larger α follow by choosing a smaller admissible α and keeping its subset; C and K are chosen after α and need not be uniform in α
--   - encoding: Cov(D) ⪯ B² I_d → finite second moment and ∫ (v·(x − m))² dD ≤ B²‖v‖² for every v; reason: quadratic-form form of the Loewner order
--   - encoding: with probability at least 1 − (failure probability) → a measurable event inside the success set has measure at least 1 − (failure probability); reason: inner-measure form; never applies a measure to a possibly non-measurable set
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 20 (printed p. 18), §8.2, displays (49)–(50) (consequence of DKP21, Theorem 1.4)

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Filter

open MeasureTheory

namespace GaussMixGated.ExactReal

/-- §8.2, displays (49)–(50) (Zheng–Xie–He, STOC 2027 #36, PDF p. 20): for every `α ∈ (0, 1)` there
are `C, K > 0` such that, for every law `D` on `ℝ^d` with finite second moments, mean `m` and
`Cov(D) ⪯ B² I_d`, and every `n ≥ C[d log(2d) + log(1/τ)]`, an i.i.d. sample `x_1, …, x_n` from
`D` contains, with probability at least `1 − τ/2`, a set `G` of at least `(1 − α/2)n` indices
with `(1/n) ∑_{i∈G} (x_i − m)(x_i − m)ᵀ ⪯ K B² I_d`. -/
theorem eq_49_50 (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (d : ℕ), 1 ≤ d → ∀ (B τ : ℝ), 0 ≤ B → 0 < τ → τ < 1 →
    ∀ (D : Measure (EuclideanSpace ℝ (Fin d))), IsProbabilityMeasure D → MemLp id 2 D →
      (∀ v : EuclideanSpace ℝ (Fin d),
        ∫ x, dotE v (x - ∫ y, y ∂D) ^ 2 ∂D ≤ B ^ 2 * ‖v‖ ^ 2) →
    ∀ n : ℕ, C * (d * Real.log (2 * d) + Real.log (1 / τ)) ≤ n →
      ∃ E : Set (Fin n → EuclideanSpace ℝ (Fin d)), MeasurableSet E ∧
        (∀ x ∈ E, ∃ G : Finset (Fin n), (1 - α / 2) * n ≤ G.card ∧
          ∀ v : EuclideanSpace ℝ (Fin d),
            (1 / (n : ℝ)) * ∑ i ∈ G, dotE v (x i - ∫ y, y ∂D) ^ 2 ≤ K * B ^ 2 * ‖v‖ ^ 2) ∧
        ENNReal.ofReal (1 - τ / 2) ≤ (Measure.pi (fun _ : Fin n => D)) E := by sorry

end GaussMixGated.ExactReal
