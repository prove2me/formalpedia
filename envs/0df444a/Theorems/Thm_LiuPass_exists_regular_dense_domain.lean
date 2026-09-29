-- Prove2me | Theorems.Thm_LiuPass_exists_regular_dense_domain
-- name    : LiuPass.exists_regular_dense_domain
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T22:34:12.98863+00:00
-- url     : https://prove2.me/theorems/ebcdc025-1e2b-4ce2-a5b4-b8c6ad661f6f
-- title:
--   Lemma 5.2: every one-way function is regular on a dense subdomain
-- statement:
--   Lemma 5.2 of the paper. Let $f$ be a one-way function. Then there are an integer-valued function
--   $r$ and sets $S_n \subseteq \{0,1\}^n$ with
--   $$|S_n| \;\ge\; \frac{2^n}{n}$$
--   such that $f$ is a one-way function over $S = \{S_n\}$ (hard to invert when the input is drawn
--   uniformly from $S_n$) and has regularity $r$ on $S$, i.e. for all sufficiently large $n$ and all
--   $x \in S_n$,
--   $$2^{r(n)-1} \;\le\; \big|f^{-1}(f(x)) \cap S_n\big| \;\le\; 2^{r(n)} .$$
--
--   The proof is an averaging argument: the $n$-bit inputs are partitioned into the $n$ classes
--   $\{x : 2^{i-1} \le |f^{-1}(f(x))| \le 2^{i}\}$, one of which must carry probability at least
--   $1/n$; taking $S_n$ to be that class makes $f$ regular on $S_n$, and density preserves one-wayness
--   up to a factor $n$. This is the step that lets the regular-OWF pseudorandom generator
--   construction be applied to an *arbitrary* one-way function, and hence the starting point of the
--   conditionally secure entropy-preserving generator of Theorem 5.5.
-- source:
--   Yanyi Liu, Rafael Pass, On One-way Functions and Kolmogorov Complexity, arXiv:2009.11514v1 (FOCS 2020), https://arxiv.org/abs/2009.11514, p. 15, Lemma 5.2 (with Claim 3 in its proof)

import Definitions.Def_LiuPass_crypto
open Finset
open scoped Classical

namespace LiuPass

open Finset
open scoped Classical

theorem exists_regular_dense_domain (U : UMachine) (f : BitStr → BitStr) (hf : IsOWF U f) :
    ∃ (r : ℕ → ℕ) (S : ℕ → BitStr → Prop),
      (∀ (n : ℕ) (x : BitStr), S n x → x.length = n) ∧
      (∀ n : ℕ, 0 < n →
        (2 : ℝ) ^ n / (n : ℝ) ≤
          ((univ.filter fun v : Fin n → Bool => S n (List.ofFn v)).card : ℝ)) ∧
      IsOWFOver U S f ∧ IsRegularOver S f r := by sorry
end LiuPass
