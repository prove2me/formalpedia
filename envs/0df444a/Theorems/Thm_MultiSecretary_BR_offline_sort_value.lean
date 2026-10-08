-- Prove2me | Theorems.Thm_MultiSecretary_BR_offline_sort_value
-- name    : MultiSecretary.BR.offline_sort_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:57:22.447084+00:00
-- url     : https://prove2.me/theorems/b41cecc5-9725-49ea-8778-7af6f12ad5dd
-- title:
--   Eq. (4), p. 7 — $V^*_{\mathrm{off}}(n,k)=\sum_j a_j\,\mathbb E[\mathfrak S^n_j]$, the offline value is the expected sort value
-- statement:
--   In the multi-secretary model, let $Z^n_j$ be the number of $a_j$-candidates among the $n$ candidates and let
--   $$\mathfrak S^n_j=\min\Big\{Z^n_j,\Big(k-\sum_{i\in[j-1]}Z^n_i\Big)_+\Big\},\qquad j\in[m],$$
--   be the number of $a_j$-candidates selected by sorting the values and keeping the $k$ largest (eq. (3)). Then for every $(n,k)\in\mathcal T$
--   $$V^*_{\mathrm{off}}(n,k)=\sum_{j\in[m]}a_j\,\mathbb E[\mathfrak S^n_j]=\sum_{j\in[m]}a_j\,\mathbb E\Big[\min\Big\{Z^n_j,\Big(k-\sum_{i\in[j-1]}Z^n_i\Big)_+\Big\}\Big].$$
--
--   This identity turns the offline benchmark, defined as an expected maximum over selections, into a function of the counts $Z^n_j$, which is what the decomposition of Proposition 1 works with.
--
--   **Formalization Note** $V^*_{\mathrm{off}}$ is defined as the expected maximum over selection vectors (p. 5), not by this formula. Lean index $i$ of `Fin m` is the paper's index $i+1$, so `a 0` is $a_1$, the largest ability. The positive part is natural-number subtraction.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Sec. 3, p. 7, eqs. (3)–(4)

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model

namespace MultiSecretary.BR

open Finset

/-- Eq. (4), p. 7: the offline value is the expected value of the sort solution (3),
`V*_off(n, k) = ∑_{j ∈ [m]} a_j E[𝔖^n_j]` with `𝔖^n_j = min{Z^n_j, (k − ∑_{i<j} Z^n_i)_+}`. -/
theorem offline_sort_value {m : ℕ} (I : Instance m) (n k : ℕ) (hk : k ≤ n) :
    I.Voff n k = ∑ j, I.a j * I.E (fun x : Fin n → Fin m => (offCount k n j x : ℝ)) := by sorry

end MultiSecretary.BR
