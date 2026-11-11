-- Prove2me | Theorems.Thm_OptAbstention_TLA_lemma_6_5
-- name    : OptAbstention.TLA.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:08:25.469193+00:00
-- url     : https://prove2.me/theorems/48ab0ef7-c1ed-4696-bd20-e242aedebfaf
-- title:
--   Lemma 6.5 (error transfer): under a good reweighting, $\Pr_{R^w_{\mathrm{test}}}[h\ne f]\le R(\Pr_D[h\ne f]+\varepsilon)$
-- statement:
--   Let $X\subseteq\mathbb R^d$, $B\ge1$, $\varepsilon,\delta\in(0,1)$, $h:X\to\{\pm1\}$, $D$ a distribution on $X$, $\mathcal C$ a concept class and $\ell=L_1(\varepsilon,B,\mathcal C,D)$. Let $S_{\mathrm{train}}$ be $m$ i.i.d. samples from $D$ with $m\ge C\,M_{D,\ell}B^2(d+1)^{2\ell}/(\varepsilon^2\delta)$, $C$ universal. Then with probability at least $1-\delta$, simultaneously for every $f\in\mathcal C$, $R\ge1$, nonempty finite $S_{\mathrm{test}}\subseteq X$ and $\big(\tfrac{R\varepsilon}{3B\binom{d+\ell}{\ell}},R\big)$-good reweighting $(u,w)$ of $(S_{\mathrm{train}},S_{\mathrm{test}})$ w.r.t. $(h,\ell)$,
--   $$\Pr_{x\sim R^w_{\mathrm{test}}}[h(x)\ne f(x)]\le R\Big(\Pr_{x\sim D}[h(x)\ne f(x)]+\varepsilon\Big).$$
--   It is the first half of the selective-error argument (Lemma 6.7, item 1).
--
--   Differences from the source:
--   - reading: h: X → {±1} and C ⊆ {±1}^X → h and every f ∈ C measurable, values ±1 as reals; reason: Pr_D[h(x) ≠ f(x)] and E_D[h(x)x^α] are defined only for measurable functions
--   - encoding: |S| ≳ E with E containing M_{D,ℓ} → n ≥ C·E in [0,∞] with a universal C fixed first; reason: M_{D,ℓ} = ∞ makes the hypothesis unsatisfiable, as in the source
--   - encoding: finite multisets → lists Fin n → X, compared through their occurrences; reason: footnote 2: occurrences are distinct elements; same instances
--   - encoding: Pr_{x∼R^w_test}[h(x) ≠ f(x)] → ∑_j w_j·1{h(T_j) ≠ f(T_j)}; reason: definition of R^w_test
--   - encoding: probability at least 1 − δ → the measure (outer measure) of the failure set is at most δ; reason: equivalent for measurable events, and never weaker
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 14, Lemma 6.5

import Mathlib
import Definitions.Def_OptAbstention_TLA_Sandwiching
import Definitions.Def_OptAbstention_TLA_Reweighting

open MeasureTheory

namespace OptAbstention.TLA

open Classical in
/-- Lemma 6.5 (error transfer), p. 14. One event over `S_train` on which the bound holds for
every `f ∈ C`, `R ≥ 1`, nonempty `S_test` and good reweighting. -/
theorem lemma_6_5 : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (X : Set (Pt d)) (D : Measure X) [IsProbabilityMeasure D] (Cl : Set (X → ℝ))
      (h : X → ℝ) (B ε δ : ℝ) (ℓ : ℕ), IsConceptClass X Cl → IsConcept X h → 1 ≤ B →
      0 < ε → ε < 1 → 0 < δ → δ < 1 → IsL1Degree D ε B Cl ℓ → ∀ m : ℕ,
      ENNReal.ofReal C * momentBound D ℓ *
          ENNReal.ofReal (B ^ 2 * ((d : ℝ) + 1) ^ (2 * ℓ) / (ε ^ 2 * δ)) ≤ (m : ENNReal) →
      (Measure.pi fun _ : Fin m => D)
        {S | ¬ ∀ f ∈ Cl, ∀ R : ℝ, 1 ≤ R → ∀ (n : ℕ) (T : Fin n → X), 0 < n →
          ∀ (u : Fin m → ℝ) (w : Fin n → ℝ),
            IsGoodReweighting S T h ℓ (R * ε / (3 * B * ((d + ℓ).choose ℓ : ℝ))) R u w →
            ∑ j, w j * (if h (T j) ≠ f (T j) then 1 else 0) ≤
              R * ((D {x | h x ≠ f x}).toReal + ε)}
        ≤ ENNReal.ofReal δ := by sorry

end OptAbstention.TLA
