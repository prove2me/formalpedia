-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_lemma_5_1
-- name    : LogGammaPolymer.Variance.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:25.977334+00:00
-- url     : https://prove2.me/theorems/71348eae-d641-4254-b270-5cb937d2e9c3
-- title:
--   Lemma 5.1 — comparison (5.2) of partition-function ratios
-- statement:
--   Let $Y$ be a configuration of positive weights on $\mathbb Z_+^2$ (the origin excepted). For $m\ge2$ and $n\ge1$,
--   $$\frac{Z_{m,n}(\xi_y>0)}{Z_{m-1,n}(\xi_y>0)}\le\frac{Z_{(1,1),(m,n)}}{Z_{(1,1),(m-1,n)}}\le\frac{Z_{m,n}(\xi_x>0)}{Z_{m-1,n}(\xi_x>0)}\qquad(5.2).$$
--
--   Restricting the path to leave the origin along the $x$-axis (resp. the $y$-axis) increases (resp. decreases) the ratio of successive partition functions, compared with the bulk partition function from $(1,1)$.
--
--   **Formalization Note** A deterministic statement, valid for every positive weight configuration.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Lemma 5.1, (5.2), p. 26

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem lemma_5_1 (Y : ℕ × ℕ → ℝ) (hY : ∀ p : ℕ × ℕ, p ≠ (0, 0) → 0 < Y p)
    (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    Zr Y m n (fun x => 0 < ξy x.1) / Zr Y (m - 1) n (fun x => 0 < ξy x.1) ≤
        Zgen Y 1 1 m n / Zgen Y 1 1 (m - 1) n ∧
      Zgen Y 1 1 m n / Zgen Y 1 1 (m - 1) n ≤
        Zr Y m n (fun x => 0 < ξx x.1) / Zr Y (m - 1) n (fun x => 0 < ξx x.1) := by sorry

end LogGammaPolymer.Variance
