-- Prove2me | Theorems.Thm_MultiSecretary_NonAdaptive_index_policy_regret
-- name    : MultiSecretary.NonAdaptive.index_policy_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:26:03.332958+00:00
-- url     : https://prove2.me/theorems/55636651-f9b9-4bf8-918d-769833a42480
-- title:
--   Lemma 3 — the non-adaptive index policy has regret V*_off − V^id_na ≤ DR − V^id_na ≤ ε⁻¹a₁√n when ε ≤ k/n
-- statement:
--   Let $0<a_m<\dots<a_1$ and masses $f_j>0$ summing to one. For every $\varepsilon\in(0,1)$ and every $1\le n$, $0\le k\le n$ with $\varepsilon\le k/n$, the non-adaptive index policy $\mathrm{id}$ of (33) satisfies
--   $$V^*_{\mathrm{off}}(n,k)-V^{\mathrm{id}}_{\mathrm{na}}(n,k)\le DR(n,k)-V^{\mathrm{id}}_{\mathrm{na}}(n,k)\le\varepsilon^{-1}a_1\sqrt n.$$
--
--   So the index policy, and hence the best non-adaptive policy, has regret $O(\sqrt n)$: the order in Theorem 3 is attained.
--
--   **Formalization Note** The $\varepsilon$ here is a free lower bound on $k/n$, not $\tfrac12\min_jf_j$, and is named `ε'` in Lean. $n\ge1$ and $k\le n$ are the paper's triangle $\mathcal T$ with $k/n$ defined. The index policy at $k=n$ uses the largest-index reading of $j_{\mathrm{id}}$ (see the definition).
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Lemma 3, p. 25

import Mathlib
import Definitions.Def_MultiSecretary_NonAdaptive_Model
import Definitions.Def_MultiSecretary_NonAdaptive_Policy

namespace MultiSecretary.NonAdaptive

open Finset

/-- Lemma 3 (p. 25): for every `ε' ∈ (0, 1)` and `(n, k)` with `ε' ≤ k/n`,
`V*_off - V^id_na ≤ DR - V^id_na ≤ ε'⁻¹ a_1 √n` for the non-adaptive index policy (33). -/
theorem index_policy_regret {m : ℕ} [NeZero m] (a f : Fin m → ℝ) (ha : IsValues a)
    (hf : IsMasses f) (ε' : ℝ) (hε'0 : 0 < ε') (hε'1 : ε' < 1) (n k : ℕ) (hn : 0 < n)
    (hkn : k ≤ n) (hk : ε' ≤ (k : ℝ) / n) :
    Voff a f n k - Vna a f k (idxPolicy f n k) ≤ DR a f n k - Vna a f k (idxPolicy f n k) ∧
    DR a f n k - Vna a f k (idxPolicy f n k) ≤ ε'⁻¹ * a 0 * Real.sqrt n := by sorry

end MultiSecretary.NonAdaptive
