-- Prove2me | Theorems.Thm_LassoDantzig_REConditions_eq_A3_shelling_bound
-- name    : LassoDantzig.REConditions.eq_A3_shelling_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T10:14:49.878286+00:00
-- url     : https://prove2.me/theorems/61db0781-baba-4738-8710-1ec3339ca0e4
-- title:
--   (A.3) — Shelling bound for the tail blocks under the cone condition
-- statement:
--   Let $\delta\in\mathbb R^M$, $J_0\subseteq\{1,\dots,M\}$, $m\ge1$, and let $J_0^c=J_1\cup\dots\cup J_K$ ($K\ge1$) be the partition of Appendix A: the blocks are pairwise disjoint, $|J_k|=m$ for $k=1,\dots,K-1$, $|J_K|\le m$, and every $|\delta_j|$ with $j$ in a later block is at most every $|\delta_j|$ with $j$ in an earlier block (so $J_k$ carries the $m$ largest $|\delta_j|$ outside $J_1\cup\dots\cup J_{k-1}$ for $k<K$, and $J_K$ is the remaining set). Then
--
--   $$
--   |\delta_{J_{k+1}}|_2\le\frac{|\delta_{J_k}|_1}{\sqrt m},\quad k=1,\dots,K-1,
--   \qquad\text{and}\qquad
--   \sum_{k=2}^K|\delta_{J_k}|_2\le\frac{|\delta_{J_0^c}|_1}{\sqrt m}.
--   $$
--
--   If moreover $|J_0|\le s$, $c_0>0$ and the cone condition (4.1) $|\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1$ holds, then, with $J_{01}=J_0\cup J_1$,
--
--   $$
--   \frac{|\delta_{J_0^c}|_1}{\sqrt m}\le\frac{c_0|\delta_{J_0}|_1}{\sqrt m}\le c_0\sqrt{\frac sm}\,|\delta_{J_0}|_2\le c_0\sqrt{\frac sm}\,|\delta_{J_{01}}|_2 .
--   $$
--
--   This is the combinatorial core of the proof of Lemma 4.1: the $\ell_2$ mass of the tail blocks is controlled by the $\ell_1$ mass outside $J_0$, and hence, via the cone condition, by the leading block.
--
--   **Formalization Note** The block partition is defined (predicate `IsShelling`), not assumed from a sorting routine; ties between equal $|\delta_j|$ may be broken arbitrarily. $n\ge1$, $M\ge2$ are standing assumptions.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, pp. 19–20, Appendix A, Eq. (A.3)

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- **(A.3)**, Bickel–Ritov–Tsybakov, arXiv:0801.1095v3, Appendix A, pp. 19–20. Let
`J0ᶜ = J 1 ∪ ⋯ ∪ J K` be the partition into consecutive blocks of `m` largest `|δ_j|`
(`IsShelling`). Then `|δ_{J(k+1)}|₂ ≤ |δ_{Jk}|₁/√m` for `k = 1, …, K−1`, hence
`∑_{k=2}^K |δ_{Jk}|₂ ≤ |δ_{J0ᶜ}|₁/√m`; and if moreover `|J0| ≤ s` and the cone condition (4.1)
holds, `|δ_{J0ᶜ}|₁/√m ≤ c₀|δ_{J0}|₁/√m ≤ c₀√(s/m)|δ_{J0}|₂ ≤ c₀√(s/m)|δ_{J01}|₂`, `J01 = J0 ∪ J 1`. -/
theorem eq_A3_shelling_bound {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (s m : ℕ) (hm : 1 ≤ m) (c0 : ℝ) (hc0 : 0 < c0)
    (δ : Fin M → ℝ) (J0 : Finset (Fin M)) (J : ℕ → Finset (Fin M)) (K : ℕ)
    (hsh : IsShelling δ J0 m J K) :
    (∀ k ∈ Finset.Ico 1 K, l2On δ (J (k + 1)) ≤ l1On δ (J k) / Real.sqrt m) ∧
    ∑ k ∈ Finset.Icc 2 K, l2On δ (J k) ≤ l1On δ J0ᶜ / Real.sqrt m ∧
    (J0.card ≤ s → ConeCond c0 J0 δ →
      l1On δ J0ᶜ / Real.sqrt m ≤ c0 * l1On δ J0 / Real.sqrt m ∧
      c0 * l1On δ J0 / Real.sqrt m ≤ c0 * Real.sqrt ((s : ℝ) / m) * l2On δ J0 ∧
      c0 * Real.sqrt ((s : ℝ) / m) * l2On δ J0 ≤
        c0 * Real.sqrt ((s : ℝ) / m) * l2On δ (J0 ∪ J 1)) := by sorry

end LassoDantzig.REConditions
