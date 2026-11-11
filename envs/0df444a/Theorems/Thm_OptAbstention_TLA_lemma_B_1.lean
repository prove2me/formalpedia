-- Prove2me | Theorems.Thm_OptAbstention_TLA_lemma_B_1
-- name    : OptAbstention.TLA.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:07:15.811312+00:00
-- url     : https://prove2.me/theorems/6446c593-1957-44cb-a25a-d6608ecb6a18
-- title:
--   Lemma B.1 (Chow concentration): uniform deviation of empirical $f\cdot p$ averages over $\mathcal P_{d,\ell,B}$
-- statement:
--   Let $d\in\mathbb N$, $\ell\ge1$, $\varepsilon,B,M>0$, $\delta\in(0,1)$, let $D$ be a distribution and $f$ a function with values in $[-M,M]$, and let $S$ be $n$ i.i.d. samples from $D$. There is a universal constant $C$ such that if $n\ge C\,M_{D,\ell}(BM)^2(d+1)^{2\ell}/(\varepsilon^2\delta)$ then, with probability at least $1-\delta$,
--   $$\sup_{p\in\mathcal P_{d,\ell,B}}\Big|\mathbb E_{x\sim U(S)}[f(x)p(x)]-\mathbb E_{x\sim D}[f(x)p(x)]\Big|<\varepsilon .$$
--   It gives the uniform concentration of polynomial and Chow moments that drives error transfer (Lemma 6.5).
--
--   **Formalization Note.** The strict bound on the supremum is stated as: some $c<\varepsilon$ bounds every term.
--
--   Differences from the source:
--   - generalization: D a distribution on ℝ^d, f: ℝ^d → [−M, M] → X ⊆ ℝ^d arbitrary, D on X, f: X → ℝ with |f| ≤ M; reason: X = ℝ^d is the source's case
--   - reading: f: ℝ^d → [−M, M] → f measurable; reason: E_D[f(x)p(x)] is defined only for measurable f
--   - encoding: |S| ≳ E with E containing M_{D,ℓ} → n ≥ C·E in [0,∞] with a universal C fixed first; reason: M_{D,ℓ} = ∞ makes the hypothesis unsatisfiable, as in the source
--   - encoding: sup_p |…| < ε → some c < ε bounds |…| for every p ∈ P_{d,ℓ,B}; reason: the same as a strict bound on the supremum
--   - encoding: probability at least 1 − δ → the measure (outer measure) of the failure set is at most δ; reason: equivalent for measurable events, and never weaker
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 37, Lemma B.1

import Mathlib
import Definitions.Def_OptAbstention_TLA_Sandwiching

open MeasureTheory

namespace OptAbstention.TLA

/-- Lemma B.1 (Chow concentration), p. 37. `|S| ≳ E` is `|S| ≥ C·E` with a universal `C`, and the
strict bound on the supremum is `∃ c < ε` bounding every term. -/
theorem lemma_B_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (d ℓ : ℕ) (X : Set (Pt d)) (D : Measure X) [IsProbabilityMeasure D] (ε B M δ : ℝ)
      (f : X → ℝ), 1 ≤ ℓ → 0 < ε → 0 < B → 0 < M → 0 < δ → δ < 1 → Measurable f →
      (∀ x, |f x| ≤ M) → ∀ n : ℕ,
      ENNReal.ofReal C * momentBound D ℓ *
          ENNReal.ofReal ((B * M) ^ 2 * ((d : ℝ) + 1) ^ (2 * ℓ) / (ε ^ 2 * δ)) ≤ (n : ENNReal) →
      (Measure.pi fun _ : Fin n => D)
        {S | ¬ ∃ c < ε, ∀ p ∈ PolyB d ℓ B,
          |(∑ i, f (S i) * peval p (S i : Pt d)) / n - ∫ x, f x * peval p (x : Pt d) ∂D| ≤ c}
        ≤ ENNReal.ofReal δ := by sorry

end OptAbstention.TLA
