-- Prove2me | Theorems.Thm_NearestDSM_theorem_3_17_one_step
-- name    : NearestDSM.theorem_3_17_one_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:57.346267+00:00
-- url     : https://prove2.me/theorems/9bc21ea1-b712-4ffc-a99b-877ada7c4603
-- title:
--   Proof of Theorem 3.17 — the one-step bound $\mathrm{dist}(y^{k+1},[y^*])\le\beta\eta\kappa^2\,\mathrm{dist}(y^k,[y^*])^2$
-- statement:
--   There exist $\epsilon>0$ and a constant $C$ with $0\le C<1$ (the paper's $\beta\eta\kappa^2$) such that, whatever vertex is chosen in step 3, one step of Algorithm 3.1 from any $y^k$ with $\mathrm{dist}(y^k,[y^*])<\epsilon$ gives
--   $$
--   \mathrm{dist}(y^{k+1},[y^*])\le C\,\mathrm{dist}(y^k,[y^*])^2 ,
--   $$
--   hence $\mathrm{dist}(y^{k+1},[y^*])<\mathrm{dist}(y^k,[y^*])^2$ whenever $y^k\notin[y^*]$.
--
--   This is the quadratic decrease of the distance to the solution set established in the proof of Theorem 3.17.
--
--   **Formalization Note** One step is the step of Algorithm 3.1 with tolerance $0$ (the iterate stays put on the solution set) and an arbitrary vertex selector; $\epsilon$ and $C$ do not depend on the selector.
--
--   Differences from the source:
--   - reading: tolerance $\mathrm{tol}$ → $\mathrm{tol}=0$, the iterate stays put once $F(y^k)=0$; reason: the convergence analysis is for the exact algorithm; with $\mathrm{tol}=0$ the while-guard stops exactly at solutions
--   - generalization: $\tilde y^k$ a vertex of $[y^k]$ "obtained from Theorem 3.15" → any vertex, via any vertex selector, with $\epsilon$ and $C$ uniform over selectors; reason: the proof says "Let $\tilde y^k$ be any vertex of $[y^k]$" and Lemma 3.16(2) covers every vertex; the procedure of Theorem 3.15 is one selector
--   - encoding: $\beta\eta\kappa^2$ with "$<\mathrm{dist}(y^k,[y^*])^2$" → a constant $0\le C<1$; $[y^*]$ → $\{y:F(y)=0\}$; reason: the strict inequality holds whenever the distance is positive
--   - encoding: size $n\ge1$ → `n + 1`; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, proof of Theorem 3.17, p.24 (Algorithm 3.1, p.20)

import Mathlib
import Definitions.Def_NearestDSM_solSet
import Definitions.Def_NearestDSM_IsVertexSelector
import Definitions.Def_NearestDSM_newtonStep

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, proof of Theorem 3.17, p.24: the one-step bound
`dist(y^{k+1}, [y∗]) ≤ βηκ² dist(y^k, [y∗])² < dist(y^k, [y∗])²` once `dist(y^k, [y∗])` is
sufficiently small. There are `ε > 0` and a constant `C ∈ [0, 1)` (the paper's `βηκ²`) such that,
for every choice of vertices, one step of Algorithm 3.1 from any `y` with `dist(y, [y∗]) < ε`
satisfies `dist(y⁺, [y∗]) ≤ C · dist(y, [y∗])²`.

**Formalization Note.** `[y∗]` is the solution set `{y | F(y) = 0}` (Lemma 3.3), `dist` is
`Metric.infDist` (3.14). One step is `newtonStep Xh σ` (Algorithm 3.1 with `tol = 0`) for any
vertex selector `σ`; `ε` and `C` do not depend on `σ`. The printed strict `<` is `C < 1`, strict
whenever `dist(y, [y∗]) > 0`. The paper's size `n` is `n + 1`. -/
theorem theorem_3_17_one_step {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ∃ ε > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ σ : Dual n → Dual n, IsVertexSelector Xh σ → ∀ y : Dual n,
        Metric.infDist y (solSet Xh) < ε →
          Metric.infDist (newtonStep Xh σ y) (solSet Xh) ≤
            C * Metric.infDist y (solSet Xh) ^ 2 := by sorry

end NearestDSM
