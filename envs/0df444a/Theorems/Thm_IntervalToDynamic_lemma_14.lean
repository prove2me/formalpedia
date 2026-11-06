-- Prove2me | Theorems.Thm_IntervalToDynamic_lemma_14
-- name    : IntervalToDynamic.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:59.892812+00:00
-- url     : https://prove2.me/theorems/73da3820-f69f-49e8-af07-bc4affa71a30
-- title:
--   Lemma 14 — surrogate regularity on $\mathcal Y$
-- statement:
--   Under the hypotheses and construction of Theorem 5, use the parameters of Table 2 and $\mathcal Y=\mathcal B(D_{\mathcal X})$.
--
--   1. Convex mode: $h$ is linear and $G_h$-Lipschitz on $\mathcal Y$.
--   2. Exp-concave mode: $h$ is $G_h$-Lipschitz, $\alpha_h$-exp-concave and $H_h$-smooth on $\mathcal Y$.
--   3. Strongly convex mode: $h$ is $G_h$-Lipschitz, $\lambda$-strongly convex and $H_h$-smooth on $\mathcal Y$.
--
--   In either curved mode, for every $u\in\mathcal X$ the gradient-shifted center satisfies
--   $$
--   c=u-H_h^{-1}\nabla h(u)\in\mathcal B(D_{\mathcal X})\subseteq\mathcal Y.
--   $$
--
--   The lemma says that the surrogates are admissible inputs for the inner algorithm and supplies the regularity used in hindsight by Theorem 6.
--
--   Differences from the source:
--   - generalization: f_t differentiable on the domain, with gradient ∇f_t → any gradient oracle with `HasGradientWithinAt` on the domain; reason: the domain may have empty interior; the gradient of a differentiable loss is such an oracle, so the printed case is included
--   - encoding: X compact convex, with Π_X and X^T presupposing a point → `X.Nonempty` inside `SatisfiesAssumptions`; reason: Π_X and comparators in X need a point; no instance of the paper is excluded
--   - generalization: G_h-Lipschitz and curvature of h on Y → `LossClass`, which adds that h is differentiable and convex on Y; reason: the surrogates are polynomials with these properties, and the goal needs them; the printed conclusions are all included
--   - encoding: h linear → `∃ dv, ∀ y', h y' = ⟪dv, y'⟫`; reason: the form of Eq. (10)
--   - encoding: H_h-smooth → `IsSmoothOn` with Mathlib's `gradient h`: gradient H_h-Lipschitz on Y; reason: h is a polynomial on all of ℝ^d, so `gradient h` is its gradient
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Lemma 14, p.30

import Mathlib
import Definitions.Def_IntervalToDynamic_roundLoss
import Definitions.Def_IntervalToDynamic_SatisfiesAssumptions
import Definitions.Def_IntervalToDynamic_LossClass
import Definitions.Def_IntervalToDynamic_Hh
import Definitions.Def_IntervalToDynamic_IsSmoothOn

namespace IntervalToDynamic

/-- Lemma 14 (surrogate regularity). Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Lemma 14, p.30.

Under the hypotheses and construction of Theorem 5, with `Y = B(D_X)` and the parameters of Table 2:
the surrogate `h` lies in the class `LossClass mode`, i.e. it is `G_h`-Lipschitz on `Y` and, in the
curved modes, `α_h`-exp-concave, respectively `λ`-strongly convex on `Y`. In the convex mode `h` is
linear. In either curved mode `h` is `H_h`-smooth on `Y`, and for every `u ∈ X` the gradient-shifted
center `c = u − H_h⁻¹ ∇h(u)` lies in `B(D_X)`.

**Formalization Note.** `h` is a polynomial on all of `ℝ^d`, so Mathlib's `gradient h` is the honest
gradient here. `mode ≠ LossMode.convex` is "either curved mode". -/
theorem lemma_14 {d : ℕ} (hd : 0 < d) (mode : LossMode) (X : Set (EuclideanSpace ℝ (Fin d))) (DX G : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (gr : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hAss : SatisfiesAssumptions mode X DX G f gr)
    (y : EuclideanSpace ℝ (Fin d)) (hy : y ∈ Metric.closedBall 0 DX) :
    LossClass mode DX G (roundLoss mode X DX G gr y) ∧
    (mode = LossMode.convex → ∃ dv : EuclideanSpace ℝ (Fin d), ∀ y', roundLoss mode X DX G gr y y' = inner ℝ dv y') ∧
    (mode ≠ LossMode.convex →
      IsSmoothOn (Metric.closedBall 0 DX) (Hh mode DX G) (roundLoss mode X DX G gr y)
        (gradient (roundLoss mode X DX G gr y)) ∧
      ∀ u ∈ X, u - (Hh mode DX G)⁻¹ • gradient (roundLoss mode X DX G gr y) u ∈
        Metric.closedBall 0 DX) := by sorry

end IntervalToDynamic
