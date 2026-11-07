-- Prove2me | Theorems.Thm_LowAccLTC_lemma_4_2_consistent_collection
-- name    : LowAccLTC.lemma_4_2_consistent_collection
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:40:31.234049+00:00
-- url     : https://prove2.me/theorems/bef21d9c-0a7a-4ba9-9a96-9df8f759226a
-- title:
--   Lemma 4.2 — an almost consistent collection of $(1-\varepsilon/3)$-close local codewords
-- statement:
--   Assume the setup and parameter bounds of Theorem 4.1 and its first three assumptions: $X$ is an $r^{-2}$-local spectral expander, $\mathcal F^jX$ is a $(\lceil6/\varepsilon\rceil,\beta)$-coboundary expander, and every $C_s$ with $|s|<r$ has distance at least $1-\varepsilon^2/36$. Let $f$ satisfy $\mathbb E_{v\in X\langle1\rangle}[\mathrm{dist}(f|_v,C_v)]\le1-\varepsilon$. Then there is a collection $\{c_s\in C_s\}_{s\in X\langle j\rangle}$ with
--   $$\Pr_{(s,s')\sim Y\langle2\rangle}\Big[c_s|_{s\cup s'}=c_{s'}|_{s\cup s'}\ \text{and}\ \mathrm{dist}(c_s,f|_s),\ \mathrm{dist}(c_{s'},f|_{s'})\le1-\tfrac\varepsilon3\Big]\ \ge\ 1-\alpha,$$
--   where $(s,s')$ is an oriented edge of $Y=\mathcal F^jX$.
--
--   Feeding this collection to the agreement-testability assumption 4 proves Theorem 4.1.
--
--   Differences from the source:
--   - reading: 'Assume the setup, parameter bounds, and first three assumptions of Theorem 4.1' → the hypotheses of Theorem 4.1 except ρ and assumption 4; reason: ρ appears only in assumption 4 and the conclusion of Theorem 4.1
--   - reading: C = Tan(X, C₀) a code, with dist(f, C) = min_{c ∈ C} dist(f, c) → the hypothesis that Tan(X, C₀) is nonempty; reason: the paper's distances to a code are minima over the code, so codes are nonempty; if a local code is empty there are no collections {c_s ∈ C_s} and the statement read literally fails (one empty line code makes C empty while almost every vertex code is unaffected)
--   - encoding: a pure r-partite simplicial complex with a positive probability measure on its top faces → PartiteComplex: a finite type of top faces with a vertex map vert t i of colour i (colours Fin r, the paper's colour i is i − 1), injective on top faces, and a positive measure μ summing to 1; reason: faces are the subsets of top faces, so this is exactly a pure weighted r-partite complex
--   - encoding: an alphabet Σ → a type A with [Finite A]; reason: alphabets are finite sets in the paper's setting (codes C ⊆ Σⁿ)
--   - encoding: λ₂ of the link graph's random-walk operator is at most λ → the variational form E_{(u,v)} g(u)g(v) ≤ λ E g² for every g of mean 0 under the link's vertex law; reason: equivalent by self-adjointness and Courant–Fischer
--   - encoding: local codewords on star(s) → words on all top faces, compared only on star(s); reason: every notion used (distance, agreement, membership in C_s) reads only the values on star(s)
--   - reading: log (base not stated) → Real.log (natural logarithm); reason: the paper does not fix the base; ln is the analyst's default and, as a lower-bound hypothesis, weaker than log₂ (ln x < log₂ x for x > 1)
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Lemma 4.2, pp.26–27 (PDF pp.29–30)

import Definitions.Def_LowAccLTC_IsLALTCVertex
import Definitions.Def_LowAccLTC_IsOneSidedLocalSpectral
import Definitions.Def_LowAccLTC_IsFacesCoboundaryExpander

namespace LowAccLTC

/-- **Lemma 4.2** (Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), pp.26–27 = PDF pp.29–30).

Assume the setup, parameter bounds and first three assumptions of Theorem 4.1, and let `f`
satisfy `E_v[dist(f|_v, C_v)] ≤ 1 - ε`. Then there is a collection `{c_s ∈ C_s}_{s ∈ X⟨j⟩}` with
`P_{(s,s') ∼ Y⟨2⟩}[c_s|_{s∪s'} = c_{s'}|_{s∪s'}, dist(c_s, f|_s) ≤ 1 - ε/3, dist(c_{s'}, f|_{s'}) ≤ 1 - ε/3] ≥ 1 - α`. -/
theorem lemma_4_2_consistent_collection {r : ℕ} {V T A : Type*} [Fintype T] [Finite A] [DecidableEq V]
    (X : PartiteComplex r V T) (C₀ : (u : Finset V) → Set (X.star u → A))
    (ε α β : ℝ) (hε : 0 < ε ∧ ε < 1) (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1)
    (hαε : α ≤ 2 * ε / 3)
    (j : ℕ) (hj : 0 < j) (hr : 0 < r)
    (hj_bound : (10 : ℝ) ^ 10 * Real.log (1 / (α * β * ε)) / ε ^ 6 ≤ j)
    (hr_bound : (10 : ℝ) ^ 8 * (j : ℝ) ^ 2 / (β * α * ε ^ 3) ≤ r)
    (hC : (X.tanner C₀).Nonempty)
    (h1 : X.IsOneSidedLocalSpectral (1 / (r : ℝ) ^ 2))
    (h2 : X.IsFacesCoboundaryExpander j ⌈6 / ε⌉₊ β)
    (h3 : ∀ s, X.IsFace s → s.card < r →
      X.HasDistAtLeast (X.star s) (X.localCode C₀ s) (1 - ε ^ 2 / 36))
    (f : T → A) (hf : X.vertexTestDist C₀ f ≤ 1 - ε) :
    ∃ c : Finset V → (T → A), (∀ s, X.IsFace s → s.card = j → c s ∈ X.localCode C₀ s) ∧
      1 - α ≤ X.E (fun t => avg (jPairs r j) (fun P =>
        ind (¬ Disagree (X.star (X.face t P.1 ∪ X.face t P.2)) (c (X.face t P.1)) (c (X.face t P.2)) ∧
          X.wdist (X.star (X.face t P.1)) (c (X.face t P.1)) f ≤ 1 - ε / 3 ∧
          X.wdist (X.star (X.face t P.2)) (c (X.face t P.2)) f ≤ 1 - ε / 3))) := by sorry

end LowAccLTC
