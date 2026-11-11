-- Prove2me | Theorems.Thm_OptAbstention_TLA_corollary_B_7
-- name    : OptAbstention.TLA.corollary_B_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:08:05.277385+00:00
-- url     : https://prove2.me/theorems/85974ae1-174a-4a8c-9840-315b2b60ea97
-- title:
--   Corollary B.7: every $v\in\Delta_R(S_{\mathrm{cln}})$ has a partner $u\in\Delta_R(S_{\mathrm{train}})$ making $(u,v)$ $(R\tau,R)$-good
-- statement:
--   Let $X\subseteq\mathbb R^d$, $D$ a distribution on $X$, $h:X\to\{\pm1\}$, $\tau>0$, $\delta\in(0,1)$, $\ell\in\mathbb N$, and let $S_{\mathrm{train}}$, $S_{\mathrm{cln}}$ be independent i.i.d. samples from $D$ with $|S_{\mathrm{train}}|,|S_{\mathrm{cln}}|\ge C\,M_{D,\ell}(d+1)^{2\ell}/(\tau\delta)^2$, $C$ universal. Then with probability at least $1-\delta$: for every $R\ge1$ and every $v\in\Delta_R(S_{\mathrm{cln}})$ there is $u\in\Delta_R(S_{\mathrm{train}})$ such that $(u,v)$ is an $(R\tau,R)$-good reweighting of $(S_{\mathrm{train}},S_{\mathrm{cln}})$ with respect to $(h,\ell)$.
--
--   It is what makes $\mathrm{LP}_{\mathrm{TLA}}$ feasible in Lemma 6.7, item 2.
--
--   Differences from the source:
--   - reading: h: X → {±1} → h measurable, values ±1 as reals; reason: the feature map built from h must be measurable (Lemma B.2 assumes measurable ψ)
--   - encoding: |S| ≳ E with E containing M_{D,ℓ} → n ≥ C·E in [0,∞] with a universal C fixed first; reason: M_{D,ℓ} = ∞ makes the hypothesis unsatisfiable, as in the source
--   - encoding: finite multisets → lists Fin n → X, compared through their occurrences; reason: footnote 2: occurrences are distinct elements; same instances
--   - encoding: probability at least 1 − δ → the measure (outer measure) of the failure set is at most δ; reason: equivalent for measurable events, and never weaker
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 41, Corollary B.7

import Mathlib
import Definitions.Def_OptAbstention_TLA_Sandwiching
import Definitions.Def_OptAbstention_TLA_Reweighting

open MeasureTheory

namespace OptAbstention.TLA

/-- Corollary B.7, p. 41: for independent i.i.d. `S_train, S_cln` from `D` with
`|S_train|, |S_cln| ≳ M_{D,ℓ}(d+1)^{2ℓ}/(τδ)²`, with probability at least `1 − δ`, for every
`R ≥ 1` and `v ∈ ∆_R(S_cln)` there is `u ∈ ∆_R(S_train)` with `(u, v)` an `(Rτ, R)`-good
reweighting of `(S_train, S_cln)` w.r.t. `(h, ℓ)`. -/
theorem corollary_B_7 : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (X : Set (Pt d)) (D : Measure X) [IsProbabilityMeasure D] (h : X → ℝ)
      (τ δ : ℝ) (ℓ : ℕ), IsConcept X h → 0 < τ → 0 < δ → δ < 1 → ∀ m n : ℕ,
      ENNReal.ofReal C * momentBound D ℓ *
          ENNReal.ofReal (((d : ℝ) + 1) ^ (2 * ℓ) / (τ * δ) ^ 2) ≤ (m : ENNReal) →
      ENNReal.ofReal C * momentBound D ℓ *
          ENNReal.ofReal (((d : ℝ) + 1) ^ (2 * ℓ) / (τ * δ) ^ 2) ≤ (n : ENNReal) →
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin n => D))
        {q | ¬ ∀ R : ℝ, 1 ≤ R → ∀ v : Fin n → ℝ, IsCappedProbVec R v →
          ∃ u : Fin m → ℝ, IsCappedProbVec R u ∧
            IsGoodReweighting q.1 q.2 h ℓ (R * τ) R u v}
        ≤ ENNReal.ofReal δ := by sorry

end OptAbstention.TLA
