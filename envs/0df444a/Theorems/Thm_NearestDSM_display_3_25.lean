-- Prove2me | Theorems.Thm_NearestDSM_display_3_25
-- name    : NearestDSM.display_3_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:31.248948+00:00
-- url     : https://prove2.me/theorems/4c9d69a0-cc9b-43b3-b9e2-25332b1f06f2
-- title:
--   (3.25) — the local Newton estimate, uniform over the vertices of $[y^*]$
-- statement:
--   For every $\eta>0$ there exists $\epsilon>0$ such that for every vertex $\tilde y^*$ of the solution set $[y^*]=\{y:F(y)=0\}$,
--   $$
--   \|F(\tilde y^*)-F(y)-V(\tilde y^*-y)\|\le\eta\,\|\tilde y^*-y\|^2\qquad\forall\,y\in B(\tilde y^*,\epsilon),\ V\in\partial F(y),
--   $$
--   where $B(\tilde y^*,\epsilon)$ is the open ball of radius $\epsilon$ around $\tilde y^*$.
--
--   This is the estimate that, together with the bound $\|\tilde V_k^{-1}\|\le\beta$, gives the quadratic one-step bound in the proof of Theorem 3.17.
--
--   **Formalization Note** $\partial F(y)$ is the set (2.7); the norm is Euclidean.
--
--   Differences from the source:
--   - generalization: a fixed $\eta$ with $0<\eta<\min\{1,1/(\beta\kappa^2)\}$ → every $\eta>0$; reason: the page's "for any fixed $\eta$" is stated here for all positive $\eta$, which contains the page's range
--   - encoding: Clarke's $\partial F(y)$ → the set (2.7); $[y^*]$ → $\{y:F(y)=0\}$ (Lemma 3.3); reason: the paper's own formula and notation
--   - encoding: size $n\ge1$ → `n + 1`; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, proof of Theorem 3.17, display (3.25) and the following sentences, p.24

import Mathlib
import Definitions.Def_NearestDSM_Fres
import Definitions.Def_NearestDSM_jacSet
import Definitions.Def_NearestDSM_solSet
open Matrix

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, display (3.25) in the proof of Theorem 3.17, p.24, uniform over the
vertices of `[y∗]`: for every fixed `η > 0` there is `ε > 0` such that
`‖F(ỹ∗) − F(y) − V(ỹ∗ − y)‖ ≤ η ‖ỹ∗ − y‖²` for every vertex `ỹ∗` of `[y∗]`, every `y` in the
open ball `B(ỹ∗, ε)` and every `V ∈ ∂F(y)`.

**Formalization Note.** `[y∗]` is the solution set `{y | F(y) = 0}` (Lemma 3.3); `∂F(y)` is
encoded by (2.7) (`jacSet`). The paper fixes `0 < η < min{1, 1/(βκ²)}`; the statement is posed for
every `η > 0`. The norm is Euclidean. The paper's size `n` is `n + 1`. -/
theorem display_3_25 {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ∀ η > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ ys ∈ Set.extremePoints ℝ (solSet Xh), ∀ y : Dual n,
      ‖y - ys‖ < ε → ∀ V ∈ jacSet Xh y,
        ‖Fres Xh ys - Fres Xh y - WithLp.toLp 2 (V *ᵥ WithLp.ofLp (ys - y))‖ ≤
          η * ‖ys - y‖ ^ 2 := by sorry

end NearestDSM
