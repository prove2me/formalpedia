-- Prove2me | Theorems.Thm_MultiSecretary_BR_sufficient_condition
-- name    : MultiSecretary.BR.sufficient_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:58:16.118584+00:00
-- url     : https://prove2.me/theorems/4152fefa-319a-49e7-b5ce-e3777c65e2a5
-- title:
--   Proposition 2 — a sufficient condition for regret $\le 3a_1M+a_1/(4\epsilon)$
-- statement:
--   In the multi-secretary model, let $\epsilon=\tfrac12\min\{f_m,\dots,f_1\}$, let $(n,k)\in\mathcal T$, and let $j_0=j_0(n,k)$ be the action index (5). Suppose $\pi\in\Pi(n,k)$ is a feasible online policy, $\tau\le n$ is a stopping time, and $M$ is a constant such that
--
--   1. $\sum_{j\in[j_0-1]}\mathbb E[S^{\pi,\tau}_j]=\sum_{j\in[j_0-1]}\mathbb E[Z^\tau_j]$,
--   2. $\mathbb E[S^{\pi,\tau}_{j_0}]\ge\mathbb E[\mathfrak S^\tau_{j_0}]-M$,
--   3. $\mathbb E[S^{\pi,\tau}_{j_0+1}]\ge\mathbb E[\mathfrak S^\tau_{j_0+1}]-M$,
--   4. $\mathbb E[\tau]\ge n-M$.
--
--   Then
--   $$V^*_{\mathrm{off}}(n,k)-V^\pi_{\mathrm{on}}(n,k)\le3a_1M+\frac{a_1}{4\epsilon}.$$
--   Here $S^{\pi,\tau}_j$, $Z^\tau_j$ and $\mathfrak S^\tau_j$ are the online, arrival and offline counts evaluated at the random time $\tau$.
--
--   The proposition reduces bounded regret to four checkable properties of a policy up to a stopping time; Corollary 1 verifies them for the Budget-Ratio policy.
--
--   **Formalization Note** Lean index $i$ of `Fin m` is the paper's index $i+1$, so `a 0` is $a_1$, the largest ability. $\tau$ is a stopping time for the filtration of the abilities: $\tau(x)$ is determined by the first $\tau(x)$ coordinates of $x$. Condition 3 is imposed only when $j_0<m$; for $j_0=m$ both counts refer to the absent level $a_{m+1}$ and are $0$, so it reads $M\ge0$, which follows from condition 4. The statement is made for each $(n,k)$; the supremum over $\mathcal T$ on the page is then immediate.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Proposition 2, p. 9

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model

namespace MultiSecretary.BR

open Finset

/-- Proposition 2 (A sufficient condition), p. 9. Fix `(n, k) ∈ T`, let `j₀ = j₀(n, k)` be the
index (5), and let `π ∈ Π(n, k)` be a feasible online policy, `τ ≤ n` a stopping time and `M` a
constant such that
(i) `∑_{j<j₀} E[S^{π,τ}_j] = ∑_{j<j₀} E[Z^τ_j]`, (ii) `E[S^{π,τ}_{j₀}] ≥ E[𝔖^τ_{j₀}] − M`,
(iii) `E[S^{π,τ}_{j₀+1}] ≥ E[𝔖^τ_{j₀+1}] − M`, (iv) `E[τ] ≥ n − M`.
Then `V*_off(n, k) − V^π_on(n, k) ≤ 3 a_1 M + a_1/(4ϵ)`.
Condition (iii) is vacuous when `j₀ = m` (both counts are `0` for the absent value `a_{m+1}`, and
`M ≥ 0` follows from (iv)). The bound for every `(n, k)` gives the page's supremum over `T`. -/
theorem sufficient_condition {m : ℕ} (I : Instance m) (n k : ℕ) (hk : k ≤ n)
    (σ : (Fin n → Fin m) → Fin n → Bool) (hσ : σ ∈ policies n m k)
    (τ : (Fin n → Fin m) → ℕ) (hτn : ∀ x, τ x ≤ n)
    (hτ : ∀ x y : Fin n → Fin m, (∀ s : Fin n, s.val < τ x → x s = y s) → τ y = τ x)
    (M : ℝ)
    (h1 : ∑ j ∈ univ.filter (fun j => j < I.actionIndex n k),
            I.E (fun x => (onCount σ (τ x) j x : ℝ)) =
          ∑ j ∈ univ.filter (fun j => j < I.actionIndex n k),
            I.E (fun x => (Z (τ x) j x : ℝ)))
    (h2 : I.E (fun x => (offCount k (τ x) (I.actionIndex n k) x : ℝ)) - M ≤
          I.E (fun x => (onCount σ (τ x) (I.actionIndex n k) x : ℝ)))
    (h3 : ∀ h : (I.actionIndex n k).val + 1 < m,
          I.E (fun x => (offCount k (τ x) ⟨(I.actionIndex n k).val + 1, h⟩ x : ℝ)) - M ≤
          I.E (fun x => (onCount σ (τ x) ⟨(I.actionIndex n k).val + 1, h⟩ x : ℝ)))
    (h4 : (n : ℝ) - M ≤ I.E (fun x => (τ x : ℝ))) :
    I.Voff n k - I.value σ ≤ 3 * I.a I.top * M + I.a I.top / (4 * I.eps) := by sorry

end MultiSecretary.BR
