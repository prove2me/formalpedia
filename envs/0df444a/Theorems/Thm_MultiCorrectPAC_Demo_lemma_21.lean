-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_lemma_21
-- name    : MultiCorrectPAC.Demo.lemma_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:46:35.846181+00:00
-- url     : https://prove2.me/theorems/13a02dcf-872d-4a1d-858d-dd87d5d9e827
-- title:
--   Lemma 21 — a partial class with d∩_N = d < ∞ has a finite cover of size at most (1 + nqk)^{M_d(n)} on every pool
-- statement:
--   Let $\mathcal Y$ be finite, $k=|\mathcal Y|\ge\ell\ge1$, $q=|\mathcal A|$, let $\mathcal H$ be a nonempty class and assume $d=d^\cap_{\mathrm N}(\mathcal H)<\infty$. For every pool $S=(x_1,\dots,x_n)$ there is a finite cover $F_S\subseteq\mathcal Y^n$ of $\mathcal H$ on $S$, which depends only on $S$ and $\mathcal H$, such that
--   $$|F_S|\le\sum_{j=0}^{\min\{n,M_d(n)\}}\binom nj(qk)^j\le(1+nqk)^{M_d(n)}.\tag{21}$$
--
--   The cover is the finite family of experts behind the agnostic learner of Theorem 16 and the prediction families of Theorem 41.
--
--   Differences from the source:
--   - encoding: h : X → A ∪ {⋆}, a class H ⊆ (A ∪ {⋆})^X with A = {A ⊆ Y : 1 ≤ |A| ≤ ℓ} → Hyp X Y = X → Option (Finset Y) (none = ⋆), with the hypothesis IsClass ℓ H (every defined value is a nonempty finset of at most ℓ labels); reason: Lean convention; exactly the same classes
--   - encoding: |Y| = k < ∞ and ℓ ≤ k (§5.1, §7) → [Fintype Y], k = Fintype.card Y, hypothesis ℓ ≤ Fintype.card Y; reason: Lean convention
--   - encoding: dimensions and sample complexities in ℕ₀ ∪ {∞}; "d < ∞" → values in ℕ∞ (⨆ resp. ⨅ over ℕ, ⊤ = ∞); "d = d∩(·) < ∞" as a natural number d with dim = d; reason: Lean convention; no junk values (⨆ ∅ = 0, ⨅ ∅ = ⊤ = ∞)
--   - encoding: pool S = (x₁, …, xₙ), repetitions allowed; F_S ⊆ Yⁿ → S : Fin n → X (not required injective); F : Finset (Fin n → Y); reason: Lean convention
--   - encoding: "depends only on S and H" → ∃ F after ∀ S and before the covering property's ∀ h ∈ H; reason: the quantifier order expresses it
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 40 (PDF 42), Lemma 21, (21)

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Dimensions
import Definitions.Def_MultiCorrectPAC_Demo_Counting

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem lemma_21 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {X Y : Type*} [Countable X] [Nonempty X] [Fintype Y]
    [DecidableEq Y] (hk : ℓ ≤ Fintype.card Y) (H : Set (Hyp X Y)) (hH : IsClass ℓ H)
    (hne : H.Nonempty) (d : ℕ) (hd : natDim H = d) (n : ℕ) (S : Fin n → X) :
    ∃ F : Finset (Fin n → Y), IsFiniteCover H S F ∧
      F.card ≤ ∑ j ∈ Finset.range (min n (mBound Y ℓ d n) + 1),
        n.choose j * (qCount Y ℓ * Fintype.card Y) ^ j ∧
      ∑ j ∈ Finset.range (min n (mBound Y ℓ d n) + 1),
        n.choose j * (qCount Y ℓ * Fintype.card Y) ^ j ≤
        (1 + n * qCount Y ℓ * Fintype.card Y) ^ mBound Y ℓ d n := by sorry

end MultiCorrectPAC.Demo
