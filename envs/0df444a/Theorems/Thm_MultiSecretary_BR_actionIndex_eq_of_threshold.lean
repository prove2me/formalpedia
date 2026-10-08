-- Prove2me | Theorems.Thm_MultiSecretary_BR_actionIndex_eq_of_threshold
-- name    : MultiSecretary.BR.actionIndex_eq_of_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:58:02.359739+00:00
-- url     : https://prove2.me/theorems/00d9e080-9c86-4038-8a98-a768b4e1070d
-- title:
--   Sec. 4, p. 17 — if $k/n\in[T_j,T_{j+1})$ then $j_0(n,k)=j$
-- statement:
--   In the multi-secretary model, with BR thresholds $T_1=0$, $T_j=\bar F(a_j)+\tfrac12 f_j$ for $j\in\{2,\dots,m\}$ and $T_{m+1}=+\infty$, and with the action index $j_0$ of (5): for every $(n,k)\in\mathcal T$ with $n\ge1$ and every $j\in[m]$,
--   $$\frac kn\in[T_j,T_{j+1})\ \Longrightarrow\ j_0(n,k)=j.$$
--
--   This links the policy's thresholds to the offline solution's action index: the interval of the initial budget ratio names the two ability levels at play.
--
--   **Formalization Note** Lean index $i$ of `Fin m` is the paper's index $i+1$, so `a 0` is $a_1$, the largest ability. For $j=m$ there is no upper condition ($T_{m+1}=+\infty$). The hypothesis $n\ge1$ makes $k/n$ the real quotient the page means.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Sec. 4, proof of Corollary 1, p. 17

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model

namespace MultiSecretary.BR

/-- Sec. 4, proof of Corollary 1, p. 17: since `T_j = F̄(a_j) + ½ f_j = F̄(a_{j+1}) − ½ f_j` for
`j ∈ {2, …, m}`, the definition (5) gives `j₀(n, k) = j` whenever `k/n ∈ [T_j, T_{j+1})`, for every
`j ∈ [m]` (`T_1 = 0`, `T_{m+1} = +∞`, so for `j = m` there is no upper condition). -/
theorem actionIndex_eq_of_threshold {m : ℕ} (I : Instance m) (n k : ℕ) (hk : k ≤ n) (hn : 0 < n)
    (j : Fin m) (hlo : I.T j ≤ (k : ℝ) / n)
    (hhi : ∀ h : j.val + 1 < m, (k : ℝ) / n < I.T ⟨j.val + 1, h⟩) :
    I.actionIndex n k = j := by sorry

end MultiSecretary.BR
