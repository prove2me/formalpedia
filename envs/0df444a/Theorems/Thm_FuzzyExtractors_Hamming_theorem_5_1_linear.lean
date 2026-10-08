-- Prove2me | Theorems.Thm_FuzzyExtractors_Hamming_theorem_5_1_linear
-- name    : FuzzyExtractors.Hamming.theorem_5_1_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:13.561986+00:00
-- url     : https://prove2.me/theorems/0fd8b662-a414-4fb0-b2da-ebee4b3854a9
-- title:
--   Theorem 5.1, linear case — the syndrome sketch is deterministic, $n-k$ symbols long, and average-case secure with loss $(n-k)f$
-- statement:
--   Let $\mathcal F$ be a finite field with $F$ elements, $f=\log F$, and let $C\subseteq\mathcal F^n$ be a linear code of dimension $k$ in which distinct codewords are at Hamming distance at least $2t+1$. Let $\mathrm{syn}:\mathcal F^n\to\mathcal F^{n-k}$ be a linear map with kernel $C$. Let $(\mathsf{SS},\mathsf{Rec})$ be the syndrome construction (Construction 3): $\mathsf{SS}(w)=\mathrm{syn}(w)$, deterministically, and $\mathsf{Rec}(w',s)$ finds a vector $e$ of Hamming weight at most $t$ with $\mathrm{syn}(e)=\mathrm{syn}(w')-s$ and outputs $w'-e$. Then for every $m$,
--   $$(\mathsf{SS},\mathsf{Rec}) \text{ is an average-case } \big(\mathcal F^n,\; m,\; m-(n-k)f,\; t\big)\text{-secure sketch,}$$
--   whose output is the $(n-k)$-symbol string $\mathrm{syn}(w)$.
--
--   This is the "Furthermore" sentence of Theorem 5.1: for linear codes the sketch can be made deterministic and short.
--
--   **Formalization Note** Determinism and the length $n-k$ are expressed by the construction itself: the sketch is a point mass with values in $\mathcal F^{n-k}$. The parity-check matrix is replaced by a linear map with kernel $C$. The efficiency clause is dropped.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4, Theorem 5.1, p. 17 (second sentence); Construction 3, p. 16

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace FuzzyExtractors.Hamming

theorem theorem_5_1_linear {F : Type} [Field F] [Fintype F] [DecidableEq F] {n k t : ℕ}
    (C : Submodule F (Fin n → F)) (hk : Module.finrank F C = k)
    (syn : (Fin n → F) →ₗ[F] (Fin (n - k) → F)) (hsyn : LinearMap.ker syn = C)
    (hdist : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → 2 * t + 1 ≤ hammingDist c c') :
    ∀ m : ℝ, IsAvgSecureSketch hammingDist m
      (m - ((n : ℝ) - k) * Real.logb 2 (Fintype.card F)) t
      (syndromeSS syn) (syndromeRec syn t) := by sorry

end FuzzyExtractors.Hamming
