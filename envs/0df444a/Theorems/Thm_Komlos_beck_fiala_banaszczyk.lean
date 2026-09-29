-- Prove2me | Theorems.Thm_Komlos_beck_fiala_banaszczyk
-- name    : Komlos.beck_fiala_banaszczyk
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-03T20:53:17.399284+00:00
-- url     : https://prove2.me/theorems/c01c7754-1430-42b7-bbd3-dba17400f3f8
-- title:
--   Discrepancy $O(\sqrt{t \log n})$ for degree-$t$ set systems
-- statement:
--   (Banaszczyk 1998, corollary.) There is a constant $C > 0$ such that every $0/1$ incidence matrix with column degree at most $t$ admits signs with each row sum at most $C\sqrt{t \log(n+2)}$ in absolute value. This has the conjectured $\sqrt{t}$ dependence of the Beck--Fiala conjecture but retains a $\sqrt{\log n}$ factor; it beats the Beck--Fiala bound $2t-1$ once $t \gg \log n$. It follows from the vector-balancing bound by scaling degree-$t$ columns to unit norm.
-- source:
--   Corollary of Banaszczyk, Random Structures & Algorithms 12 (1998), via scaling incidence columns; stated e.g. in Bansal--Dadush--Garg, An algorithm for Komlos conjecture matching Banaszczyk's bound, https://arxiv.org/abs/1605.02882

import Mathlib
import Definitions.Def_Komlos_model

namespace Komlos

theorem beck_fiala_banaszczyk :
    ∃ C : ℝ, 0 < C ∧ ∀ (t n m : ℕ) (A : Fin m → Fin n → ℝ),
      (∀ i j, A i j = 0 ∨ A i j = 1) →
      (∀ j, ({i | A i j = 1} : Finset (Fin m)).card ≤ t) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ i, |∑ j, A i j * ε j| ≤ C * Real.sqrt (t * Real.log (n + 2)) := by sorry

end Komlos
