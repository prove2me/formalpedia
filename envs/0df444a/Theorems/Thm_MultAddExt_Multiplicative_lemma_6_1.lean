-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_lemma_6_1
-- name    : MultAddExt.Multiplicative.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:47:24.257732+00:00
-- url     : https://prove2.me/theorems/5c5a8a64-ef7e-408a-b5db-3a1d093ad544
-- title:
--   Lemma 6.1 — chopping a min-entropy source into a convex combination of block-prefix sources (as printed; see insight I1)
-- statement:
--   Let $\varepsilon>0$ and $k,n,b,\ell\in\mathbb N$ with $k\le n$ and $\ell\cdot b=n$. Let $X$ be a distribution on $\{0,1\}^n$ with $H_\infty(X)\ge k$, viewed as $X=(X_1,\dots,X_\ell)$ with $X_i\in\{0,1\}^b$, and write $x_{[1,i]}$ for the first $i$ blocks of $x$. Then there are distributions $X^{(0)},\dots,X^{(\ell)}$ on $\{0,1\}^n$ and weights $\lambda_i\ge 0$ with $\sum_{i=0}^{\ell}\lambda_i=1$ and
--   $$X=\sum_{i=0}^{\ell}\lambda_i X^{(i)},$$
--   such that:
--
--   1. the supports of the $X^{(i)}$ with $\lambda_i>0$ are pairwise disjoint and their union is $\mathrm{Supp}(X)$; moreover, for $i\ge 1$ and $x\in\mathrm{Supp}(X)$, whether $x\in\mathrm{Supp}(X^{(i)})$ depends only on $x_{[1,i]}$;
--   2. $\lambda_0\le\varepsilon$, and for all $i\ge 1$, either $\lambda_i\ge\varepsilon/(2n)$ or $\lambda_i=0$;
--   3. for all $i\ge 1$ with $\lambda_i>0$, $H_\infty\bigl(X^{(i)}_{[1,i]}\bigr)\ge k/2-\log(2n/\varepsilon)$;
--   4. for all $i\ge 1$ with $\lambda_i>0$ and every $v\in\mathrm{Supp}(X^{(i)}_{[1,i]})$, $\Pr[X^{(i)}_{[1,i]}=v]\ge 2^{-k/2-b-\log(2n/\varepsilon)}$;
--   5. for all $i\ge 1$ with $\lambda_i>0$, $X^{(i)}_{[1,i]}$ has the law of $X_{[1,i]}\mid (X\in\mathrm{Supp}(X^{(i)}))$.
--
--   This structural decomposition feeds Lemma 6.3: each piece has a prefix that is a block source with high min-entropy and no light points. The statement is posed exactly as printed; it fails for $n=\ell=0$ (insight I1).
--
--   Differences from the source:
--   - encoding: a (joint) distribution on a finite set → a real mass function p with IsDist p (nonnegative, summing to 1); H∞ = minEntropy (−log₂ of the maximum mass), laws of functions by pushforward; reason: finite distributions are exactly such mass functions; same instances
--   - encoding: prefix x_[1,i] ∈ {0,1}^{ib} and the distribution X^(i)_[1,i] → prefixBits b i x ∈ {0,1}^n (the first ib bits kept, the rest set to 0) and its pushforward; reason: the padding map is injective on prefixes, so point probabilities, supports and min-entropy are unchanged
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 30 (PDF 34), Lemma 6.1

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Lemma 6.1** (chopping), p. 30, stated as printed. For `ε > 0` and `k, n, b, ℓ ∈ ℕ` with
`k ≤ n` and `ℓ·b = n`, every distribution `X` on `{0,1}ⁿ = ({0,1}^b)^ℓ` with `H∞(X) ≥ k` is a
convex combination `∑_{i=0}^{ℓ} λ_i X^(i)` with properties 1–5 of the paper; `x_[1,i]` is
`prefixBits b i x`. -/
theorem lemma_6_1 (ε : ℝ) (hε : 0 < ε) (k n b ℓ : ℕ) (hkn : k ≤ n) (hn : ℓ * b = n)
    (X : (Fin n → Bool) → ℝ) (hX : IsDist X) (hk : (k : ℝ) ≤ minEntropy X) :
    ∃ (Xs : Fin (ℓ + 1) → (Fin n → Bool) → ℝ) (lam : Fin (ℓ + 1) → ℝ),
      (∀ i, IsDist (Xs i)) ∧ (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧
      (∀ x, X x = ∑ i, lam i * Xs i x) ∧
      -- Property 1: the supports of the `X^(i)` with `λ_i > 0` partition `Supp(X)` …
      (∀ i j, i ≠ j → 0 < lam i → 0 < lam j → Disjoint (support (Xs i)) (support (Xs j))) ∧
      (∀ x, x ∈ support X ↔ ∃ i, 0 < lam i ∧ x ∈ support (Xs i)) ∧
      -- … and for `i ≥ 1`, membership of `x ∈ Supp(X)` in `Supp(X^(i))` depends on `x_[1,i]` only
      (∀ i : Fin (ℓ + 1), 1 ≤ i.val → ∀ x ∈ support X, ∀ y ∈ support X,
        prefixBits b i.val x = prefixBits b i.val y →
          (x ∈ support (Xs i) ↔ y ∈ support (Xs i))) ∧
      -- Property 2
      lam 0 ≤ ε ∧ (∀ i : Fin (ℓ + 1), 1 ≤ i.val → ε / (2 * n) ≤ lam i ∨ lam i = 0) ∧
      -- Property 3
      (∀ i : Fin (ℓ + 1), 1 ≤ i.val → 0 < lam i →
        (k : ℝ) / 2 - Real.logb 2 (2 * n / ε) ≤
          minEntropy (pushforward (prefixBits b i.val) (Xs i))) ∧
      -- Property 4
      (∀ i : Fin (ℓ + 1), 1 ≤ i.val → 0 < lam i →
        ∀ v ∈ support (pushforward (prefixBits b i.val) (Xs i)),
          (2 : ℝ) ^ (-(k : ℝ) / 2 - b - Real.logb 2 (2 * n / ε)) ≤
            pushforward (prefixBits b i.val) (Xs i) v) ∧
      -- Property 5
      (∀ i : Fin (ℓ + 1), 1 ≤ i.val → 0 < lam i →
        pushforward (prefixBits b i.val) (Xs i) =
          pushforward (prefixBits b i.val) (condDist X (support (Xs i)))) := by sorry

end MultAddExt.Multiplicative
