-- Prove2me | Theorems.Thm_LowAccLTC_lemma_4_3_restriction_lists
-- name    : LowAccLTC.lemma_4_3_restriction_lists
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:39:30.161842+00:00
-- url     : https://prove2.me/theorems/b730a549-052d-42b2-83cb-6eea6a46a6b4
-- title:
--   Lemma 4.3 — lists $L(s)\subseteq C_s$ on which restriction is a bijection on almost every edge of $\mathcal C^jX$
-- statement:
--   Let $\varepsilon,\alpha,\beta\in(0,1)$ with $\alpha\le2\varepsilon/3$, and integers $j,r>0$ with $j\ge10^{10}\log(1/(\alpha\beta\varepsilon))/\varepsilon^6$ and $r\ge10^8j^2/(\beta\alpha\varepsilon^3)$. Let $C=\mathrm{Tan}(X,C_0)$ be an HDX code on a weighted $r$-partite complex $X$ that is an $r^{-2}$-local spectral expander and in which every local code $C_s$, $|s|<r$, has distance at least $1-\varepsilon^2/36$. Let $f$ satisfy $\mathbb E_{v\in X\langle1\rangle}[\mathrm{dist}(f|_v,C_v)]\le1-\varepsilon$.
--
--   Then there is an assignment of a list $L(s)\subseteq C_s$ to every vertex $s$ of the containment complex $\mathcal C^jX$ (faces of sizes $j,2j,3j$) such that, for each of the three kinds of edges $s\subset t$ ($j\subset2j$, $j\subset3j$, $2j\subset3j$), with probability at least
--   $$1-\frac{\beta\alpha}{100}$$
--   over a random such edge:
--   1. $L(s)$ and $L(t)$ are nonempty and contain at most $6/\varepsilon$ codewords;
--   2. every codeword of $L(s)$ is $(1-\varepsilon/3)$-close to $f|_s$ and every codeword of $L(t)$ is $(1-\varepsilon/3)$-close to $f|_t$;
--   3. the restriction map $\mathrm{Res}_{s,t}:L(s)\to L(t)$, $c\mapsto c|_t$, is a bijection.
--
--   These lists are the input to the coboundary-expansion step of Lemma 4.2.
--
--   Differences from the source:
--   - generalization: probability ≥ 1 − βα/100 over a random edge s ⊂ t of C^jX → the same bound for each of the three edge types j ⊂ 2j, j ⊂ 3j, 2j ⊂ 3j under its induced law; reason: the per-type bound implies the bound for the mixture over a random edge; the proof (p.38) establishes it per type
--   - reading: 'Let ε, α, β, r, j, f be as above' → the setup and parameter bounds of Theorem 4.1, its assumptions 1 and 3, and the §4.3 standing f; reason: Lemma 4.3 'requires only the first and third assumptions of Theorem 4.1' (p.30)
--   - reading: C = Tan(X, C₀) a code, with dist(f, C) = min_{c ∈ C} dist(f, c) → the hypothesis that Tan(X, C₀) is nonempty; reason: the paper's distances to a code are minima over the code, so codes are nonempty; if a local code is empty there are no collections {c_s ∈ C_s} and the statement read literally fails (one empty line code makes C empty while almost every vertex code is unaffected)
--   - encoding: a pure r-partite simplicial complex with a positive probability measure on its top faces → PartiteComplex: a finite type of top faces with a vertex map vert t i of colour i (colours Fin r, the paper's colour i is i − 1), injective on top faces, and a positive measure μ summing to 1; reason: faces are the subsets of top faces, so this is exactly a pure weighted r-partite complex
--   - encoding: an alphabet Σ → a type A with [Finite A]; reason: alphabets are finite sets in the paper's setting (codes C ⊆ Σⁿ)
--   - encoding: λ₂ of the link graph's random-walk operator is at most λ → the variational form E_{(u,v)} g(u)g(v) ≤ λ E g² for every g of mean 0 under the link's vertex law; reason: equivalent by self-adjointness and Courant–Fischer
--   - encoding: lists L(s) ⊆ C_s of local codewords → finite sets of words on all top faces, members of C_s, pairwise different on star(s); restriction to t is agreement on star(t); reason: each list of local codewords has such a representation and conversely
--   - reading: log (base not stated) → Real.log (natural logarithm); reason: the paper does not fix the base; ln is the analyst's default and, as a lower-bound hypothesis, weaker than log₂ (ln x < log₂ x for x > 1)
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Lemma 4.3, p.30 (PDF p.33); standing assumptions §4.3, p.30

import Definitions.Def_LowAccLTC_ListPair
import Definitions.Def_LowAccLTC_IsLALTCVertex
import Definitions.Def_LowAccLTC_IsOneSidedLocalSpectral

namespace LowAccLTC

/-- **Lemma 4.3** (Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), p.30 = PDF p.33).

Under the setup and parameter bounds of Theorem 4.1, its assumptions 1 (`X` is an
`r^{-2}`-local spectral expander) and 3 (all `C_s`, `|s| < r`, have distance `≥ 1 - ε²/36`), and
for `f` with `E_v[dist(f|_v, C_v)] ≤ 1 - ε` (§4.3, p.30), there are lists `L(s) ⊆ C_s` on the
vertices of `C^j X` (faces of size `j, 2j, 3j`) such that, with probability at least
`1 - βα/100` over a random edge `s ⊂ t` of `C^j X`, the lists are nonempty of size `≤ 6/ε`,
consist of `(1 - ε/3)`-close codewords, and restriction `L(s) → L(t)` is a bijection. The bound
holds for each of the three edge types `j ⊂ 2j`, `j ⊂ 3j`, `2j ⊂ 3j` under its induced law. -/
theorem lemma_4_3_restriction_lists {r : ℕ} {V T A : Type*} [Fintype T] [Finite A]
    (X : PartiteComplex r V T) (C₀ : (u : Finset V) → Set (X.star u → A))
    (ε α β : ℝ) (hε : 0 < ε ∧ ε < 1) (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1)
    (hαε : α ≤ 2 * ε / 3)
    (j : ℕ) (hj : 0 < j) (hr : 0 < r)
    (hj_bound : (10 : ℝ) ^ 10 * Real.log (1 / (α * β * ε)) / ε ^ 6 ≤ j)
    (hr_bound : (10 : ℝ) ^ 8 * (j : ℝ) ^ 2 / (β * α * ε ^ 3) ≤ r)
    (hC : (X.tanner C₀).Nonempty)
    (h1 : X.IsOneSidedLocalSpectral (1 / (r : ℝ) ^ 2))
    (h3 : ∀ s, X.IsFace s → s.card < r →
      X.HasDistAtLeast (X.star s) (X.localCode C₀ s) (1 - ε ^ 2 / 36))
    (f : T → A) (hf : X.vertexTestDist C₀ f ≤ 1 - ε) :
    ∃ L : Finset V → Finset (T → A),
      (∀ s, X.IsFace s → (s.card = j ∨ s.card = 2 * j ∨ s.card = 3 * j) →
        (∀ c ∈ L s, c ∈ X.localCode C₀ s) ∧
        ∀ c ∈ L s, ∀ c' ∈ L s, (∀ x ∈ X.star s, c x = c' x) → c = c') ∧
      ∀ ab ∈ [(j, 2 * j), (j, 3 * j), (2 * j, 3 * j)],
        1 - β * α / 100 ≤ X.E (fun t => avg (nestedPairs r ab.1 ab.2) (fun P =>
          ind (X.IsGoodListPair f ε L (X.face t P.1) (X.face t P.2)))) := by sorry

end LowAccLTC
