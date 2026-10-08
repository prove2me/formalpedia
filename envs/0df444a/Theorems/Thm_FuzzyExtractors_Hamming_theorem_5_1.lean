-- Prove2me | Theorems.Thm_FuzzyExtractors_Hamming_theorem_5_1
-- name    : FuzzyExtractors.Hamming.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:38.155768+00:00
-- url     : https://prove2.me/theorems/f31a8cd3-19b0-4f53-9404-3ad76e5f1d7f
-- title:
--   Theorem 5.1 — the code-offset sketch of an $[n,k,2t+1]_{\mathcal F}$ code is an average-case $(\mathcal F^n, m, m-(n-k)f, t)$-secure sketch
-- statement:
--   Let $\mathcal F$ be a finite additive group with $F=|\mathcal F|$ elements, $f=\log F$, and let $C\subseteq\mathcal F^n$ be a nonempty code with $K=|C|$ codewords in which distinct codewords are at Hamming distance at least $2t+1$; write $kf=\log K$ (so $k=\log_F K$). Let $(\mathsf{SS},\mathsf{Rec})$ be the code-offset construction (Construction 2): $\mathsf{SS}(w)=w-c$ for a uniformly random $c\in C$, and $\mathsf{Rec}(w',s)$ decodes $w'-s$ to a codeword $c$ and outputs $c+s$. Then for every $m$,
--   $$(\mathsf{SS},\mathsf{Rec}) \text{ is an average-case } \big(\mathcal F^n,\; m,\; m-(nf-\log K),\; t\big)\text{-secure sketch,}$$
--   and $nf-\log K=(n-k)f$.
--
--   This is the sketch half of the mission's goal; combined with universal hashing it gives Theorem 5.2.
--
--   **Formalization Note** The paper says "one can construct"; we state the claim for the code-offset construction itself, which is what the proof gives and is stronger. The code need not be linear and $k$ need not be an integer, so $(n-k)f$ is written $n\log F-\log K$. $\mathcal F$ may be any finite additive commutative group (the paper views it as an additive cyclic group). The efficiency clause is dropped; the linear "Furthermore" sentence is the separate item `theorem_5_1_linear`.
-- source:
--   Dodis, Ostrovsky, Reyzin & Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4, Theorem 5.1, p. 17 (first sentence); Construction 2, p. 16

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

namespace FuzzyExtractors.Hamming

theorem theorem_5_1 {F : Type} [Fintype F] [DecidableEq F] [AddCommGroup F] {n : ℕ}
    (C : Finset (Fin n → F)) (hC : C.Nonempty) (t : ℕ) (hdist : MinDistGe C (2 * t + 1)) :
    ∀ m : ℝ, IsAvgSecureSketch hammingDist m
      (m - ((n : ℝ) * Real.logb 2 (Fintype.card F) - Real.logb 2 C.card)) t
      (codeOffsetSS C hC) (codeOffsetRec C t) := by sorry

end FuzzyExtractors.Hamming
