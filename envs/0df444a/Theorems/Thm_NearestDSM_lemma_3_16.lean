-- Prove2me | Theorems.Thm_NearestDSM_lemma_3_16
-- name    : NearestDSM.lemma_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:10.439234+00:00
-- url     : https://prove2.me/theorems/0b3fe5e8-57d2-4e55-b257-9ae93955ce90
-- title:
--   Lemma 3.16 — classes near $[y^*]$ have points and vertices near $[y^*]$ and $\operatorname{ext}[y^*]$
-- statement:
--   Suppose $F(y^*)=0$. Then there exist $\epsilon_0>0$ and $\kappa>0$ such that for every $\epsilon\in(0,\epsilon_0]$ and every $y\in\mathbb R^{2n-1}$ with $\mathrm{dist}(y,[y^*])<\epsilon$:
--
--   1. $\mathrm{dist}(\tilde y,[y^*])<\kappa\,\epsilon$ for every $\tilde y\in[y]$;
--   2. $\mathrm{dist}(\tilde y,\operatorname{ext}[y^*])<\kappa\,\epsilon$ for every $\tilde y\in\operatorname{ext}[y]$.
--
--   Here $\mathrm{dist}(y,S)=\inf_{s\in S}\|y-s\|$. The lemma is what turns the Newton estimate at a vertex of $[y^*]$ into a quadratic decrease of $\mathrm{dist}(y^k,[y^*])$.
--
--   **Formalization Note** $\mathrm{dist}$ is `Metric.infDist` for the Euclidean norm, and $\operatorname{ext}$ is the set of extreme points.
--
--   Differences from the source:
--   - reading: "there exist $\epsilon>0$ and $\kappa>0$ such that for any $y$ with $\mathrm{dist}(y,[y^*])<\epsilon$ … $<\kappa\cdot\epsilon$" → there are $\epsilon_0,\kappa>0$ such that the bounds hold for every $\epsilon\in(0,\epsilon_0]$; reason: the proof of Theorem 3.17 applies the lemma with $\epsilon=\mathrm{dist}(y^k,[y^*])$ at every step, and the lemma's proof bounds everything by constant multiples of $\|y-y^*\|$; this reading contains the literal one ($\epsilon=\epsilon_0$)
--   - encoding: size $n\ge1$ → `n + 1`; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Lemma 3.16, p.21 ((3.14) p.20; use in the proof of Theorem 3.17, p.24)

import Mathlib
import Definitions.Def_NearestDSM_Fres
import Definitions.Def_NearestDSM_equivClass

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Lemma 3.16, p.21. Suppose `F(y∗) = 0`. Then there exist `ε > 0` and
`κ > 0` such that for any `y` with `dist(y, [y∗]) < ε`:
1. `dist(ỹ, [y∗]) < κ · ε` for every `ỹ ∈ [y]`;
2. `dist(ỹ, ext[y∗]) < κ · ε` for every `ỹ ∈ ext[y]`.

Stated in the form the proof of Theorem 3.17 (p.24) uses: there are `ε₀ > 0` and `κ > 0` such
that both bounds hold for **every** `ε ∈ (0, ε₀]`.

**Formalization Note.** `dist(y, S) = inf_{s ∈ S} ‖y − s‖` (3.14) is `Metric.infDist` for the
Euclidean norm; `ext[y]` is `Set.extremePoints ℝ [y]`. The paper's size `n` is `n + 1`. -/
theorem lemma_3_16 {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (ys : Dual n) (hs : Fres Xh ys = 0) :
    ∃ ε₀ > 0, ∃ κ > 0, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ y : Dual n,
      Metric.infDist y (equivClass Xh ys) < ε →
        (∀ yt ∈ equivClass Xh y, Metric.infDist yt (equivClass Xh ys) < κ * ε) ∧
        (∀ yt ∈ Set.extremePoints ℝ (equivClass Xh y),
          Metric.infDist yt (Set.extremePoints ℝ (equivClass Xh ys)) < κ * ε) := by sorry

end NearestDSM
