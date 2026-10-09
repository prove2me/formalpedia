-- Prove2me | Theorems.Thm_ModernOnlineLearning_Portfolio_theorem_10_4
-- name    : ModernOnlineLearning.Portfolio.theorem_10_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:38:47.28098+00:00
-- url     : https://prove2.me/theorems/664b7012-762e-45a8-9f93-2e7895684b86
-- title:
--   Theorem 10.4, p. 174 — method-of-types bound on type-class size
-- statement:
--   Let an alphabet have $d\ge2$ symbols, and let $T\ge1$. For a realizable type $n=(n_1,\ldots,n_d)$ of length-$T$ sequences, let $\mathcal T_T(n)$ be the set of sequences of that type. Then
--
--   $$|\mathcal T_T(n)|\le\prod_{i=1}^{d}n_i^{-n_iT},$$
--
--   with $0^0=1$. The bound controls how many stock-choice paths share one empirical allocation.
--
--   **Formalization Note** A type is required to arise from an actual sequence, exactly as the source’s $n\in Q$ condition. Real exponentiation has the required $0^0$ convention.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 10.4, p. 174

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Setting
set_option autoImplicit false

namespace ModernOnlineLearning.Portfolio

/-- Theorem 10.4, p. 174: the method-of-types cardinality bound. -/
theorem theorem_10_4 {d T : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T)
    (n : Fin d → ℝ) (hn : n ∈ possibleTypes d T) :
    (typeClass (d := d) (T := T) n).card ≤
      ∏ i : Fin d, (n i) ^ (-(n i) * (T : ℝ)) := by sorry

end ModernOnlineLearning.Portfolio
