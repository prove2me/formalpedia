-- Prove2me | Theorems.Thm_Komlos_bansal_jiang_komlos_bound
-- name    : Komlos.bansal_jiang_komlos_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-03T20:54:53.269827+00:00
-- url     : https://prove2.me/theorems/6111c72b-15e3-401a-b4f9-801cb79df5a0
-- title:
--   Komlós discrepancy $\tilde{O}((\log n)^{1/4})$ (Bansal–Jiang)
-- statement:
--   There are constants $C > 0$ and $\gamma > 0$ such that for all $n, m$ and all vectors $v_1, \dots, v_n \in \mathbb{R}^m$ with $\lVert v_i \rVert_2 \le 1$, some signs $\varepsilon_i \in \{\pm 1\}$ give $\max_j |\sum_i \varepsilon_i v_{ij}| \le C (\log(n+2))^{1/4} (\log\log(n+8))^{\gamma}$ — the $\tilde{O}((\log n)^{1/4})$ bound, with the hidden $\mathrm{poly}(\log\log n)$ factor rendered as $(\log\log(n+8))^{\gamma}$ and both constants quantified before all instances. The first improvement over Banaszczyk's $O(\sqrt{\log n})$ since 1998.
-- source:
--   N. Bansal, H. Jiang, Decoupling via affine spectral-independence: Beck-Fiala and Komlos bounds beyond Banaszczyk, 2025, https://arxiv.org/abs/2508.03961, Theorem 1.2

import Mathlib
import Definitions.Def_Komlos_model

namespace Komlos

theorem bansal_jiang_komlos_bound :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)), (∀ i, ‖v i‖ ≤ 1) →
        ∃ ε : Fin n → ℝ, IsSignVector ε ∧
          ∀ j, |∑ i, ε i * v i j| ≤
            C * Real.log (n + 2) ^ ((1 : ℝ) / 4) *
              Real.log (Real.log (n + 8)) ^ γ := by sorry

end Komlos
