-- Prove2me | Theorems.Thm_OnlineLearningOCO_Agnostic_eq_3_1
-- name    : OnlineLearningOCO.Agnostic.eq_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:10.863242+00:00
-- url     : https://prove2.me/theorems/b3f8314c-b0a1-4a9a-ac12-4a277b2d8c60
-- title:
--   Equation (3.1) — the number of experts is Σ_{L ≤ Ldim} C(T, L) ≤ (eT/Ldim)^Ldim
-- statement:
--   Fix a horizon $T$ and an integer $L$ with $1 \le L \le T$. The experts Expert$(i_1,\dots,i_\ell)$ of §3.2.1 with $\ell \le L$ and $1 \le i_1 < \dots < i_\ell \le T$ correspond to the subsets of $\{1,\dots,T\}$ of size at most $L$. Their number is
--
--   $$
--   d = \sum_{j=0}^{L} \binom{T}{j} \le \Big(\frac{eT}{L}\Big)^{L}.
--   $$
--
--   With $L = \operatorname{Ldim}(H)$ this is the bound on the number of experts used in the proof of Theorem 3.6: it gives $\log d \le L \ln(eT/L)$, which turns the $\sqrt{\log(d)\,T}$ regret of Weighted Majority into the $\sqrt{\operatorname{Ldim}(H)\ln(eT/\operatorname{Ldim}(H))\,T}$ bound.
--
--   **Formalization Note** Subsets of rounds are represented 0-based as subsets of $\{0,\dots,T-1\}$. The hypothesis $1 \le L \le T$ is the paper's implicit range: for $T = 1$, $L = 3$ the left side is $2$ while $(e/3)^3 < 1$.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 168, §3.2.1, equation (3.1)

import Mathlib

namespace OnlineLearningOCO.Agnostic

/-- Equation (3.1), p. 168. The experts Expert(I) with `I ⊆ {0,…,T−1}` and `|I| ≤ L` number
`d = ∑_{j=0}^{L} C(T, j)`, and for `1 ≤ L ≤ T`, `∑_{j=0}^{L} C(T, j) ≤ (eT/L)^L`. -/
theorem eq_3_1 (T L : ℕ) (hL : 1 ≤ L) (hLT : L ≤ T) :
    ((Finset.range T).powerset.filter (fun I ↦ I.card ≤ L)).card =
        ∑ j ∈ Finset.range (L + 1), T.choose j ∧
      (∑ j ∈ Finset.range (L + 1), (T.choose j : ℝ)) ≤ (Real.exp 1 * T / L) ^ L := by sorry

end OnlineLearningOCO.Agnostic
