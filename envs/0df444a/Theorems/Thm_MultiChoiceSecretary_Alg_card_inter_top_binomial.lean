-- Prove2me | Theorems.Thm_MultiChoiceSecretary_Alg_card_inter_top_binomial
-- name    : MultiChoiceSecretary.Alg.card_inter_top_binomial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:22.427367+00:00
-- url     : https://prove2.me/theorems/6026a78a-9dd7-4d9a-b35c-2b45fd8c6d48
-- title:
--   Proof sketch of Theorem 2.1, PDF p. 2 — |Y ∩ T| has the distribution B(k, 1/2)
-- statement:
--   Let $S$ be a finite set of $n$ real numbers, $1 \le k \le n$, and let $T$ be the $k$ largest elements of $S$. Let $Y$ be the set of the first $m$ arrivals of a uniformly random order of $S$, with $m \sim B(n,1/2)$ independent. Then $|Y \cap T|$ has the binomial distribution $B(k, 1/2)$: for every $r \ge 0$,
--
--   $$\Pr(|Y \cap T| = r) = \binom{k}{r}2^{-k}.$$
--
--   This is the "first consequence" of $Y$ being a uniform random subset in the proof sketch of Theorem 2.1.
--
--   **Formalization Note.** The hypothesis $k \le n$ is added: the page leaves it implicit. For $n < k$ the set $T$ has $n$ elements and $|Y \cap T| \sim B(n,1/2)$, not $B(k,1/2)$.
-- source:
--   Kleinberg, A multiple-choice secretary algorithm with applications to online auctions, SODA 2005, PDF p. 2, proof sketch of Theorem 2.1, "First, the random variable |Y ∩ T| has the distribution B(k, 1/2)."

import Mathlib
import Definitions.Def_MultiChoiceSecretary_Alg_Setting

namespace MultiChoiceSecretary.Alg

theorem card_inter_top_binomial (S : Finset ℝ) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ S.card) :
    ∀ r : ℕ, splitAvg S (fun Y => if (Y ∩ topK S k).card = r then 1 else 0) =
      (k.choose r : ℝ) / 2 ^ k := by sorry

end MultiChoiceSecretary.Alg
