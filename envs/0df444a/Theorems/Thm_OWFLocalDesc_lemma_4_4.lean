-- Prove2me | Theorems.Thm_OWFLocalDesc_lemma_4_4
-- name    : OWFLocalDesc.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:44:27.499462+00:00
-- url     : https://prove2.me/theorems/80c8692c-b907-4305-8de1-ef75cbc97a14
-- title:
--   Lemma 4.4 (Random-query encoding): rank, near-uniform labels, entropy
-- statement:
--   Fix positive integers $n,L,m$, a real $\varepsilon\ge0$ and a real $r\ge0$. Let $S:\{0,1\}^n\to\mathbb F_2^L$ have bias at most $\varepsilon$ on uniform inputs. Let $X=(X_1,\dots,X_m)$ be independent uniform $n$-bit points and let $M_X$ be the $m\times L$ matrix over $\mathbb F_2$ whose $i$-th row is $S(X_i)$. Then:
--
--   1. $$\Pr[\operatorname{rank}M_X<m]\le 2^{m-L}+(1+\varepsilon)^m-1;\tag{1}$$
--   2. the statistical distance between $(X,M_XU_L)$ and $(X,U_m)$, with $U_L,U_m$ uniform and independent of $X$, is at most the right side of (1);
--   3. if an $\mathbb F_2^L$-valued random variable $V$, independent of $X$, has support of size at most $2^r$, then
--   $$H(M_XV\mid X)\ \ge\ H(V)-\log\big(1+2^{r-m}(1+\varepsilon)^m\big).\tag{2}$$
--
--   This lemma says that small-bias measurements of a vector at random points give nearly uniform labels for a uniform vector, and lose little entropy for a vector of bounded support.
--
--   **Formalization Note** Probabilities are counting fractions over $(\{0,1\}^n)^m$. $V$ is a probability vector $p_V$ on $\mathbb F_2^L$ with at most $2^r$ nonzero entries, and $H(M_XV\mid X)$ is the average over $x$ of the entropy of $y\mapsto\sum_{v:M_xv=y}p_V(v)$.
--
--   Differences from the source:
--   - encoding: random variables X, U_L, U_m, V; statistical distance; conditional entropy → counting fractions over ({0,1}^n)^m; ½ Σ_{x,y} |P₁(x,y) − P₂(x,y)|; V as a probability vector with ≤ 2^r nonzero entries; H(·|X) as the average of the published `FuchsVdGraaf.entropy` of the conditional laws; reason: the paper's own definitions (§2, §4.1) written out; no instance changes
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Lemma 4.4, p.18

import Mathlib
import Definitions.Def_OWFLocalDesc_HasBiasAtMost
import Definitions.Def_OWFLocalDesc_queryMatrix
import Definitions.Def_FuchsVdGraaf_entropy
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Lemma 4.4 (Random-query encoding).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Lemma 4.4, p.18: "Fix
positive integers n, L, m, a real ε ≥ 0 and a real r ≥ 0. Let S : {0,1}^n → F_2^L have bias at
most ε on uniform inputs … Let X_1,…,X_m be independent uniform points. … Let M_X be the matrix whose
ith row is S(X_i). Then (1) Pr[rank M_X < m] ≤ 2^{m−L} + (1+ε)^m − 1. The statistical distance
between (X, M_X U_L) and (X, U_m) is at most the right side of Equation (1), where the uniform
variables are independent of X. If an F_2^L-valued random variable V is independent of X and has
support of size at most 2^r, then (2) H(M_X V | X) ≥ H(V) − log(1 + 2^{r−m}(1+ε)^m)."

**Formalization Note.** `X` is uniform on `({0,1}ⁿ)^m` (mass `2^{−mn}`). The statistical distance
is `½ ∑_{x,y} |P₁(x,y) − P₂(x,y)|` over `({0,1}ⁿ)^m × 𝔽₂^m`. `V` is any probability vector
`p_V` on `𝔽₂^L` with at most `2^r` nonzero entries; `H(M_X V | X)` is the average over `x` of
the entropy of the law `y ↦ ∑_{v : M_x v = y} p_V(v)`. Entropy is the published Shannon entropy in
bits `FuchsVdGraaf.entropy p = −∑ p log₂ p` (with `0 log 0 = 0`). -/
theorem lemma_4_4 (n L m : ℕ) (hn : 0 < n) (hL : 0 < L) (hm : 0 < m) (ε r : ℝ) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (S : (Fin n → Bool) → (Fin L → ZMod 2)) (hS : HasBiasAtMost S ε) :
    (open Classical in
      ((Finset.univ.filter fun X : Fin m → Fin n → Bool => (queryMatrix S X).rank < m).card : ℝ) /
          (2 : ℝ) ^ (m * n) ≤
        (2 : ℝ) ^ ((m : ℤ) - L) + (1 + ε) ^ m - 1) ∧
    (open Classical in
      (1 / 2) * ∑ X : Fin m → Fin n → Bool, ∑ y : Fin m → ZMod 2,
          |1 / (2 : ℝ) ^ (m * n) *
              (((Finset.univ.filter fun u : Fin L → ZMod 2 =>
                  (queryMatrix S X).mulVec u = y).card : ℝ) / (2 : ℝ) ^ L) -
            1 / (2 : ℝ) ^ (m * n) * (1 / (2 : ℝ) ^ m)| ≤
        (2 : ℝ) ^ ((m : ℤ) - L) + (1 + ε) ^ m - 1) ∧
    ∀ pV : (Fin L → ZMod 2) → ℝ, (∀ v, 0 ≤ pV v) → ∑ v, pV v = 1 →
      (open Classical in ((Finset.univ.filter fun v => pV v ≠ 0).card : ℝ)) ≤ (2 : ℝ) ^ r →
        FuchsVdGraaf.entropy pV - Real.logb 2 (1 + (2 : ℝ) ^ (r - m) * (1 + ε) ^ m) ≤
          (∑ X : Fin m → Fin n → Bool,
              FuchsVdGraaf.entropy (fun y : Fin m → ZMod 2 =>
                open Classical in
                ∑ v ∈ Finset.univ.filter (fun v => (queryMatrix S X).mulVec v = y), pV v)) /
            (2 : ℝ) ^ (m * n) := by sorry

end OWFLocalDesc
