-- Prove2me | Theorems.Thm_MultiSecretary_NonAdaptive_small_budget_regret
-- name    : MultiSecretary.NonAdaptive.small_budget_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:26:34.586729+00:00
-- url     : https://prove2.me/theorems/cc5fd541-3a27-47a1-8900-01faf9a0a95c
-- title:
--   Lemma 4 — for k ≤ n(f₁ − ϵ), V*_off(n, k) − V*_na(n, k) ≤ a₂/(4ϵ)
-- statement:
--   Let $m\ge2$, $0<a_m<\dots<a_1$, masses $f_j>0$ summing to one, and $\epsilon=\tfrac12\min_jf_j$. If $k\le n(f_1-\epsilon)$, then
--   $$V^*_{\mathrm{off}}(n,k)-V^*_{\mathrm{na}}(n,k)\le\frac{a_2}{4\epsilon}.$$
--
--   For small budgets non-adaptivity costs only a constant, so the range of $(n,k)$ in Theorem 3 cannot be extended to this regime.
--
--   **Formalization Note** Lean index $j\in\{0,\dots,m-1\}$ is the paper's index $j+1$, so `a 0` is the largest value $a_1$, `f 0` is $f_1$ and `f (Fin.rev 0)` is $f_m$. The value $a_2$ is `a ⟨1, _⟩`. The hypothesis $m\ge2$ is added so that $a_2$ exists; the paper's convention $a_{m+1}<a_m$ gives no value for $a_2$ when $m=1$.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Lemma 4, p. 25

import Mathlib
import Definitions.Def_MultiSecretary_NonAdaptive_Model
import Definitions.Def_MultiSecretary_NonAdaptive_Policy

namespace MultiSecretary.NonAdaptive

open Finset

/-- Lemma 4 (p. 25): with `ϵ = ½ min f_j` and `k ≤ n (f_1 - ϵ)`,
`V*_off(n, k) - V*_na(n, k) ≤ a_2/(4ϵ)` (requires `m ≥ 2` for `a_2` to exist). -/
theorem small_budget_regret {m : ℕ} [NeZero m] (hm : 2 ≤ m) (a f : Fin m → ℝ) (ha : IsValues a)
    (hf : IsMasses f) (n k : ℕ) (hk : (k : ℝ) ≤ n * (f 0 - eps f)) :
    Voff a f n k - VstarNa a f n k ≤ a ⟨1, by omega⟩ / (4 * eps f) := by sorry

end MultiSecretary.NonAdaptive
