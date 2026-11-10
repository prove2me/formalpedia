-- Prove2me | Theorems.Thm_MulticlassOmni_Lipschitz_lemma_B_1
-- name    : MulticlassOmni.Lipschitz.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:13:56.830186+00:00
-- url     : https://prove2.me/theorems/6f2888ce-adb3-41c4-9135-b08fc2dd1a52
-- title:
--   Lemma B.1 — zero-sum sphere packing of size $2^{-Ck}\varepsilon^{-(k-2)/2}$, a multiple of four and above any prescribed constant
-- statement:
--   There is an absolute constant $C>0$ such that, for every prescribed absolute constant $M\in\mathbb R$, there is $\varepsilon_0>0$ with the following property. For every integer $k\ge3$ and every $0<\varepsilon\le\varepsilon_0$ there is a finite set $X\subseteq[-1,1]^k$ with
--   $$|X|\ge2^{-Ck}\varepsilon^{-(k-2)/2},\qquad \sum_{y=1}^kx_y=0,\quad\|x\|_2^2=k/4\ (x\in X),\qquad\langle x,x'\rangle\le\tfrac k4(1-8000\varepsilon)\ (x\ne x'\in X),$$
--   $|X|$ a multiple of four, and $|X|>M$.
--
--   Differences from the source:
--   - reading: 'We may take |X| to be a multiple of four. By decreasing ε0, we may also require |X| to exceed any prescribed absolute constant, uniformly over k ≥ 3' → both are asserted: ∃ C > 0, ∀ M, ∃ ε0 > 0, ∀ k ≥ 3, ∀ ε ∈ (0, ε0], ∃ X with all properties, 4 ∣ |X| and M < |X| (the same C for every M); reason: the stronger reading of the optional clauses; M = 0 gives the lemma's first sentence together with divisibility
--   - encoding: labels [k] = {1, …, k} → Fin k, the source label y is the index y − 1 (label 1 is index 0); reason: relabeling; same instances
--   - encoding: a finite set X in real k-dimensional space, with Euclidean sums and a real-power cardinality bound → X : Finset (Fin k → ℝ), explicit coordinate sums for the inner product and squared norm, and real casts of k and X.card in real powers and inequalities; reason: the same finite sets, Euclidean geometry and real exponents; no natural-number truncation
-- source:
--   Hu, Luo, Schneider, Yang (2026), Sample Complexity of Multiclass Omniprediction, supplied PDF (SHA-256 aaa73474…584f0, citation basis published; STOC 2027 submission), Lemma B.1, p. 54

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_Packings

namespace MulticlassOmni.Lipschitz

/-- **Lemma B.1 (Packing the zero-sum sphere)**, Hu, Luo, Schneider, Yang (2026), p. 54.
There is an absolute constant `C > 0` such that for every prescribed absolute constant `M` there
is `ε₀ > 0` with: for every integer `k ≥ 3` and every `0 < ε ≤ ε₀` there is a finite set
`X ⊆ [-1, 1]^k` with `|X| ≥ 2^{-Ck} ε^{-(k-2)/2}`, `∑_y x_y = 0` and `‖x‖₂² = k/4` for `x ∈ X`,
`⟨x, x'⟩ ≤ (k/4)(1 - 8000ε)` for distinct `x, x' ∈ X`, `|X|` a multiple of four, and `|X| > M`. -/
theorem lemma_B_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∃ X : Finset (Fin k → ℝ),
          (2 : ℝ) ^ (-C * k) * ε ^ (-((k : ℝ) - 2) / 2) ≤ (X.card : ℝ) ∧
          IsZeroSumPacking k ε X ∧ 4 ∣ X.card ∧ M < (X.card : ℝ) := by sorry

end MulticlassOmni.Lipschitz
