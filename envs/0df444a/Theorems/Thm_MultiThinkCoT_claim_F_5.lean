-- Prove2me | Theorems.Thm_MultiThinkCoT_claim_F_5
-- name    : MultiThinkCoT.claim_F_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:44.501794+00:00
-- url     : https://prove2.me/theorems/d19f0e2f-b109-4f31-95dd-eaccdf5c1b69
-- title:
--   Claim F.5 — training error at most $\prod_k 2\sqrt{\epsilon_k(1-\epsilon_k)}$
-- statement:
--   In Algorithm 1, for every input training set $S_{\mathrm{e2e}}=\{(x^{(i)},y^{(i)})\}_{i\le m}$, every Consistent oracle and adversary and all parameters $K$, $M_\star$, $\delta$, every run that does not return at line 12 (every executed round has $\epsilon_k\le0.25$) outputs a predictor $\hat h_K$ with
--
--   $$
--   \frac1m\sum_{i=1}^m\mathbf 1\big[\hat h_K(x^{(i)})\neq y^{(i)}\big]\ \le\ \prod_{k}2\sqrt{\epsilon_k(1-\epsilon_k)},
--   $$
--
--   the product running over the executed rounds.
--
--   This is the AdaBoost training-error bound for the boosting recursion of Algorithm 1, used in Lemma F.3.
--
--   **Formalization Note** "The final predictor $\hat h_K$" is the output of line 14 or line 17. A line-12 return breaks the printed bound: with $K=1$, $m=1$, $y^{(1)}=1$ and $\hat f_1\equiv0$ we get $\epsilon_1=1$, and the constant-$0$ output has error $1>0$. After a line-14 return at round $k'$ the last factor is $2\sqrt{0\cdot1}=0$, matching the paper's argument that the error is then $0$.
--
--   Differences from the source:
--   - reading: the final predictor ĥ_K of Algorithm 1, for every input training set → every run in the support that does not return at line 12, i.e. all executed ϵ_k ≤ 0.25 (outputs of line 14 or 17); reason: the line-12 constant violates the bound (K = 1, m = 1, y = 1, f̂_1 ≡ 0: ϵ_1 = 1, error 1 > 0); the proof on p.57 treats only line-14 and line-17 returns
--   - encoding: Π_{k=1}^K 2√(ϵ_k(1 − ϵ_k)) → the product over the executed rounds' ϵ_k; reason: after a line-14 return at round k' later rounds do not exist; the factor at k' is 0, as the paper's case analysis gives error 0
--   - generalization: a run of Algorithm 1 with a Consistent oracle, an adversary of Definition 2.3 and δ ∈ (0, 1) → every run of alg1 for any oracle function, any adversary function, any δ ∈ ℝ, any M⋆ and any m; reason: the bound concerns only the boosting recursion of lines 10–17 on the recorded ϵ_k and holds whatever produced the f̂_k; the paper's runs are among these
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix F, Claim F.5, p.57 (PDF p.57)

import Mathlib
import Definitions.Def_MultiThinkCoT_alg1

namespace MultiThinkCoT

/-- **Claim F.5**, p.57 (PDF p.57).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

In Algorithm 1, for every input training set `S_e2e`, the empirical error of the final predictor
`ĥ_K` is bounded as `(1/m) Σ_{i=1}^m 1[ĥ_K(x(i)) ≠ y(i)] ≤ Π_{k=1}^K 2√(ϵ_k(1 − ϵ_k))`.

**Formalization Note.**
* "The final predictor `ĥ_K`" is the output of line 14 or line 17: the statement is for every run
  in which every executed round has `ϵ_k ≤ 0.25`, i.e. the run does not return at line 12. (A
  line-12 return breaks the bound: `K = 1`, `m = 1`, `y(1) = 1`, `f̂_1 ≡ 0` gives `ϵ_1 = 1`, output
  constant `0` with error `1 > 0 = 2√(ϵ_1(1 − ϵ_1))`.) The proof on p.57 treats exactly these runs.
* The product runs over the executed rounds (`Outcome.errs`): all `K` rounds after a line-17
  return; rounds `1, …, k'` after a line-14 return at round `k'`, where the last factor is
  `2√(0 · 1) = 0` and the paper's proof shows the error is `0`.
* It holds for every oracle, adversary, `K`, `M⋆`, `δ` and cost functions.
-/
theorem claim_F_5 (T : ℕ) (O : List (List Bool × Bool) → Gen) (oc : ℕ → ℕ → ℕ) (ec : ℕ → ℕ)
    (K Mst : ℕ) (δ : ℝ) {m : ℕ} (xs : Fin m → List Bool) (ys : Fin m → Bool)
    (adv : History m → Finset (Fin m) → Gen) :
    ∀ r ∈ (alg1 T O oc ec K Mst δ xs ys adv).support, (∀ e ∈ r.errs, e ≤ 1 / 4) →
      1 / (m : ℝ) * ∑ i, (if r.pred.eval T (xs i) ≠ ys i then (1 : ℝ) else 0) ≤
        (r.errs.map fun e => 2 * Real.sqrt (e * (1 - e))).prod := by sorry

end MultiThinkCoT
