-- Prove2me | Theorems.Thm_LimitsLifting_Approximation_lemma_4_7
-- name    : LimitsLifting.Approximation.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:39:01.626199+00:00
-- url     : https://prove2.me/theorems/9123ae9a-30f7-44b5-9eba-eb09a5706cb4
-- title:
--   Lemma 4.7 — Rectangle Lemma: a Rectangle Scheme with error density $n^{-w}$, width $O(w)$ and query alignment exists
-- statement:
--   For every sufficiently large real $\Delta$ there are a constant $K>0$ and $n_0$ such that, for every $n\ge n_0$ and $m=n^\Delta$, there is a deterministic Rectangle Scheme: given a parameter $0<w\le n$ and a rectangle $R\subseteq[m]^n\times\{0,1\}^{mn}$, it outputs a partition $\bigsqcup_i R_i$ of $R$ and error sets $X_{\mathrm{err}}\subseteq[m]^n$, $Y_{\mathrm{err}}\subseteq\{0,1\}^{mn}$, both of density at most $n^{-w}$, such that for each $i$ one of the following holds:
--   1. **Structured case:** $R_i$ is $\rho_i$-structured for some $\rho_i$ of width at most $Kw$;
--   2. **Error case:** $R_i\subseteq X_{\mathrm{err}}\times\{0,1\}^{mn}\cup[m]^n\times Y_{\mathrm{err}}$.
--
--   Further, **query alignment** holds: for every $x\in[m]^n\setminus X_{\mathrm{err}}$ there is $I_x\subseteq[n]$ with $|I_x|\le Kw$ such that every structured $R_i$ meeting $\{x\}\times\{0,1\}^{mn}$ has $\mathrm{fix}(\rho_i)\subseteq I_x$.
--
--   The lemma is the existence statement behind the approximation model $\mathcal M_w$: every other result of the mission is stated for an arbitrary scheme with these properties.
--
--   **Formalization Note** "$O(w)$" is $Kw$ with $K$ fixed before $n$; pieces are nonempty, pairwise disjoint and cover $R$.
--
--   Differences from the source:
--   - encoding: m = n^Δ for a large enough constant Δ → real Δ ≥ Δ₀, with integer m and (m : ℝ) = (n : ℝ)^Δ; reason: preserves all admissible real exponents; block length is an integer, with no rounding or restriction to integer exponents.
--   - encoding: a parameter w ≤ n → a real parameter 0 < w ≤ n; reason: the parameter is Ω(w_Res) > 0 wherever it is used; w ≤ 0 makes the density bound vacuous.
--   - encoding: [m], [n] → Fin m, Fin n; reason: index shift, same instances.
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), Lemma 4.7 (citing [GGKS20, Lemma 4.5]), printed p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_LimitsLifting_Approximation_ApproxModel
import Definitions.Def_LimitsLifting_Approximation_CanonicalCover
import Definitions.Def_LimitsLifting_Approximation_RectangleScheme
open MultiplierAssoc206.Resolution

namespace LimitsLifting.Approximation

theorem lemma_4_7 :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ → ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n m : ℕ, n₀ ≤ n → (m : ℝ) = (n : ℝ) ^ Δ →
      ∃ σ : RectScheme n m, IsRectangleScheme n m K σ := by sorry

end LimitsLifting.Approximation
