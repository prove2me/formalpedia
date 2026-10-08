-- Prove2me | Theorems.Thm_MultiChoiceSecretary_Alg_modVal_given_card
-- name    : MultiChoiceSecretary.Alg.modVal_given_card
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:21.58122+00:00
-- url     : https://prove2.me/theorems/fc9a843d-5231-4fc2-96fa-814940bdb8fe
-- title:
--   Proof sketch of Theorem 2.1, PDF p. 2 — given |Y ∩ T| = r, the expected modified value of Y is (r/k)v
-- statement:
--   Let $S$ be a finite set of $n$ non-negative reals, $1 \le k \le n$, $T$ the $k$ largest elements of $S$ and $v$ their sum. The modified value of a set is the sum of its elements lying in $T$. Let $Y$ be the set of the first $m$ arrivals of a uniformly random order of $S$, $m \sim B(n,1/2)$ independent. Conditional on $|Y\cap T| = r$, the expected modified value of $Y$ is $(r/k)v$. Multiplied by the probability of the event, this reads: for every $r \ge 0$,
--
--   $$\mathbb E\big[\mathrm{modval}(Y)\,\mathbf 1\{|Y\cap T| = r\}\big] = \binom{k}{r}2^{-k}\cdot\frac{r}{k}\,v.$$
--
--   This is the "second consequence" in the proof sketch of Theorem 2.1.
--
--   **Formalization Note.** The conditional expectation is stated multiplied by $\Pr(|Y\cap T| = r) = \binom{k}{r}2^{-k}$, which avoids dividing by a probability. The hypothesis $k \le n$ is added, as for the distribution of $|Y \cap T|$.
-- source:
--   Kleinberg, A multiple-choice secretary algorithm with applications to online auctions, SODA 2005, PDF p. 2, proof sketch of Theorem 2.1, "Second, conditional on the event |Y ∩ T| = r, the expected modified value of Y is (r/k)v."

import Mathlib
import Definitions.Def_MultiChoiceSecretary_Alg_Setting

namespace MultiChoiceSecretary.Alg

theorem modVal_given_card (S : Finset ℝ) (hS : ∀ x ∈ S, 0 ≤ x) (k : ℕ) (hk : 1 ≤ k)
    (hkn : k ≤ S.card) :
    ∀ r : ℕ, splitAvg S (fun Y => if (Y ∩ topK S k).card = r then modVal S k Y else 0) =
      (k.choose r : ℝ) / 2 ^ k * ((r : ℝ) / k * topSum S k) := by sorry

end MultiChoiceSecretary.Alg
