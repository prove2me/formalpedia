-- Prove2me | Theorems.Thm_MultiSecretary_BR_offline_sort_decomposition
-- name    : MultiSecretary.BR.offline_sort_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:57:46.254289+00:00
-- url     : https://prove2.me/theorems/ef9d770d-d852-4c17-abbd-2568eb74ef30
-- title:
--   Proposition 1 — offline sort decomposition: on $\mathcal T_j$ the offline value is carried by $a_1,\dots,a_{j+1}$ up to $\pm a_1/(4\epsilon)$
-- statement:
--   In the multi-secretary model, let $\epsilon=\tfrac12\min\{f_m,\dots,f_1\}$, fix $j\in\{1,\dots,m\}$, and let $(n,k)\in\mathcal T_j=\{(n,k)\in\mathcal T:j_0(n,k)=j\}$, where $j_0$ is the action index (5). Then
--   $$\sum_{i\in[j-1]}\mathbb E[Z^n_i]-\frac1{4\epsilon}\le\sum_{i\in[j-1]}\mathbb E[\mathfrak S^n_i]\qquad\text{and}\qquad\sum_{i=j+2}^m\mathbb E[\mathfrak S^n_i]\le\frac1{4\epsilon},\tag{6}$$
--   and consequently
--   $$V^*_{\mathrm{off}}(n,k)=\sum_{i\in[j-1]}a_i\,\mathbb E[Z^n_i]+a_j\,\mathbb E[\mathfrak S^n_j]+a_{j+1}\,\mathbb E[\mathfrak S^n_{j+1}]\pm\frac{a_1}{4\epsilon},\tag{7}$$
--   where $y=x\pm z$ means $|y-x|\le z$.
--
--   Up to a constant, the offline solution takes every candidate above $a_j$, none below $a_{j+1}$, and all its action is at the two levels $a_j,a_{j+1}$. This is the target an online policy must imitate to have bounded regret.
--
--   **Formalization Note** Lean index $i$ of `Fin m` is the paper's index $i+1$, so `a 0` is $a_1$, the largest ability. For $j=m$ the term $a_{j+1}\mathbb E[\mathfrak S^n_{j+1}]$ is $0$ (the paper's $f_{m+1}=0$). The sum $\sum_{i=j+2}^m$ is over Lean indices $i\ge j+2$.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Proposition 1, p. 8, eqs. (6)–(7)

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model

namespace MultiSecretary.BR

open Finset

/-- Proposition 1 (Offline sort decomposition), p. 8. Let `ϵ = ½ min_j f_j` and `j ∈ [m]`. For all
`(n, k) ∈ T_j = {(n, k) ∈ T : j₀(n, k) = j}`:
`∑_{i<j} E[Z^n_i] − 1/(4ϵ) ≤ ∑_{i<j} E[𝔖^n_i]` and `∑_{i=j+2}^m E[𝔖^n_i] ≤ 1/(4ϵ)` (6), and
`V*_off(n, k) = ∑_{i<j} a_i E[Z^n_i] + a_j E[𝔖^n_j] + a_{j+1} E[𝔖^n_{j+1}] ± a_1/(4ϵ)` (7), where
`y = x ± z` means `|y − x| ≤ z` and the `a_{j+1}` term is `0` when `j = m` (`f_{m+1} = 0`).
Lean index `i` is the paper's `i + 1`. -/
theorem offline_sort_decomposition {m : ℕ} (I : Instance m) (j : Fin m) (n k : ℕ) (hk : k ≤ n)
    (hj : I.actionIndex n k = j) :
    (∑ i ∈ univ.filter (fun i => i < j), I.E (fun x : Fin n → Fin m => (Z n i x : ℝ))
        - 1 / (4 * I.eps) ≤
      ∑ i ∈ univ.filter (fun i => i < j), I.E (fun x : Fin n → Fin m => (offCount k n i x : ℝ))) ∧
    (∑ i ∈ univ.filter (fun i : Fin m => j.val + 2 ≤ i.val),
        I.E (fun x : Fin n → Fin m => (offCount k n i x : ℝ)) ≤ 1 / (4 * I.eps)) ∧
    |I.Voff n k -
        (∑ i ∈ univ.filter (fun i => i < j), I.a i * I.E (fun x : Fin n → Fin m => (Z n i x : ℝ))
          + I.a j * I.E (fun x : Fin n → Fin m => (offCount k n j x : ℝ))
          + (if h : j.val + 1 < m then
              I.a ⟨j.val + 1, h⟩ * I.E (fun x : Fin n → Fin m => (offCount k n ⟨j.val + 1, h⟩ x : ℝ))
            else 0))| ≤ I.a I.top / (4 * I.eps) := by sorry

end MultiSecretary.BR
