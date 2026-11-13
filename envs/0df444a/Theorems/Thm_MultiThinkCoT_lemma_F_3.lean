-- Prove2me | Theorems.Thm_MultiThinkCoT_lemma_F_3
-- name    : MultiThinkCoT.lemma_F_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:51.7609+00:00
-- url     : https://prove2.me/theorems/0d24c5b1-e212-4a5b-a364-5a4ce9a82dbd
-- title:
--   Lemma F.3 — zero training error once $K\ge8\log m$ (corrected: $K\ge1$)
-- statement:
--   For every training set $S_{\mathrm{e2e}}=\{(x^{(i)},y^{(i)})\}_{i\le m}$, every Consistent oracle and adversary, every $M_\star$ and $\delta$, and every number of rounds $K\ge1$ with
--
--   $$
--   K\ \ge\ 8\log m,
--   $$
--
--   every run of Algorithm 1 on $S_{\mathrm{e2e}}$ in which $\epsilon_k\le0.25$ for all executed rounds $k$ returns a predictor $\hat h_K$ with zero training error: $\sum_{i=1}^m\mathbf 1[\hat h_K(x^{(i)})\neq y^{(i)}]=0$.
--
--   Combined with Lemma F.2 this shows that Algorithm 1 outputs, with high probability, a member of $H_{\mathrm{boost}}(K)$ consistent with the whole training set.
--
--   **Formalization Note** $K\ge1$ corrects the printed statement. With $K=0$, $m=1$, $y^{(1)}=0$ the condition $K\ge8\log1=0$ holds, but line 17 returns the empty weighted majority, the constant $1$, with training error $1$. Natural logarithm.
--
--   Differences from the source:
--   - correction: any K ≥ 8 log m (K = 0 allowed when m = 1) → 1 ≤ K and 8 log m ≤ K; reason: counterexample: K = 0, m = 1, y(1) = 0; the hypothesis on the ϵ_k is vacuous and line 17 returns the constant 1 (ties to 1) with training error 1
--   - reading: ϵ_k ≤ 0.25 for all k ∈ [K] when running Algorithm 1 → every executed round of the run has ϵ_k ≤ 0.25; reason: after a line-14 return no further rounds exist
--   - generalization: a run of Algorithm 1 with a Consistent oracle, an adversary of Definition 2.3 and δ ∈ (0, 1) → every run of alg1 for any oracle function, any adversary function, any δ ∈ ℝ, any M⋆ and any m; reason: the bound concerns only the boosting recursion of lines 10–17 on the recorded ϵ_k and holds whatever produced the f̂_k; the paper's runs are among these
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix F, Lemma F.3, p.55 (PDF p.55)

import Mathlib
import Definitions.Def_MultiThinkCoT_alg1

namespace MultiThinkCoT

/-- **Lemma F.3 (Zero training error via exponential decay)**, p.55 (PDF p.55) (corrected:
`K ≥ 1`).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

For every training set `S_e2e = {(x(i), y(i))}_{i ≤ m}`, as long as `ϵ_k ≤ 0.25` for all `k ∈ [K]`
when running Algorithm 1 on `S_e2e`, for any `K ≥ 8 log m` (and `K ≥ 1`) the predictor `ĥ_K`
achieves zero training error: `Σ_{i=1}^m 1[ĥ_K(x(i)) ≠ y(i)] = 0`.

**Formalization Note.**
* Correction `K ≥ 1`: with `K = 0`, `m = 1`, `y(1) = 0` the condition `K ≥ 8 log 1 = 0` holds and
  "`ϵ_k ≤ 0.25` for all `k ∈ [K]`" is vacuous, but line 17 returns the empty weighted majority,
  the constant `1` (ties to `1`), with training error `1`.
* "`ϵ_k ≤ 0.25` for all `k ∈ [K]`" is: every executed round of the run has `ϵ_k ≤ 0.25`
  (`Outcome.errs`); it holds for every run in the support of Algorithm 1 with these parameters,
  for every oracle, adversary, `M⋆`, `δ` and cost functions. `log` is natural.
-/
theorem lemma_F_3 (T : ℕ) (O : List (List Bool × Bool) → Gen) (oc : ℕ → ℕ → ℕ) (ec : ℕ → ℕ)
    (K Mst : ℕ) (δ : ℝ) {m : ℕ} (xs : Fin m → List Bool) (ys : Fin m → Bool)
    (adv : History m → Finset (Fin m) → Gen) (hK1 : 1 ≤ K) (hK : 8 * Real.log m ≤ K) :
    ∀ r ∈ (alg1 T O oc ec K Mst δ xs ys adv).support, (∀ e ∈ r.errs, e ≤ 1 / 4) →
      ∑ i, (if r.pred.eval T (xs i) ≠ ys i then (1 : ℕ) else 0) = 0 := by sorry

end MultiThinkCoT
