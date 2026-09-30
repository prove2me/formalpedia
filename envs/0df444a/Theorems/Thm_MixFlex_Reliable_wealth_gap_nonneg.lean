-- Prove2me | Theorems.Thm_MixFlex_Reliable_wealth_gap_nonneg
-- name    : MixFlex.Reliable.wealth_gap_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:59:54.655902+00:00
-- url     : https://prove2.me/theorems/73690244-1c45-482f-a958-ff5cc62e2833
-- title:
--   (A-4)–(A-6) — pooling all dedicated capacity into the flexible resource never lowers terminal wealth
-- statement:
--   Consider the SD and SF networks with perfectly reliable resources, a common margin $p>0$ and a common marginal cost $c$ for every resource, the flexible one included. Take any dedicated investment $K=(K_1,\dots,K_N)$ and let the flexible network invest the total $K_{N+1}=\sum_{n}K_n$. For every demand realization $x=(x_1,\dots,x_N)$ the terminal wealths (A-4)–(A-5) satisfy
--   $$
--   w^{SF}\Big(\sum_{n=1}^N K_n\Big)-w^{SD}(K)=p\Big(\min\Big\{\sum_{n=1}^N x_n,\sum_{n=1}^N K_n\Big\}-\sum_{n=1}^N\min\{x_n,K_n\}\Big)\ge 0 .
--   $$
--
--   This pathwise comparison is the whole content of the paper's proof of Proposition 4: every later step compares distributions or objectives derived from it.
--
--   **Formalization Note** The statement is pointwise in the sample point and needs no sign condition on $K$ or on demand; the inequality $\min\{\sum x_n,\sum K_n\}\ge\sum\min\{x_n,K_n\}$ holds for all reals.
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, pp. 52–53, Appendix A, proof of PROPOSITION 4(i), (A-4)–(A-6)

import Mathlib
import Definitions.Def_MixFlex_Reliable_Model

namespace MixFlex.Reliable
theorem wealth_gap_nonneg (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    (X : Ω → Fin N → ℝ) (K : Fin N → ℝ) (ω : Ω) :
    wealthSF P X P.c (∑ n, K n) ω - wealthSD P X K ω =
        P.p * (min (∑ n, X ω n) (∑ n, K n) - ∑ n, min (X ω n) (K n)) ∧
      0 ≤ wealthSF P X P.c (∑ n, K n) ω - wealthSD P X K ω := by sorry
end MixFlex.Reliable
