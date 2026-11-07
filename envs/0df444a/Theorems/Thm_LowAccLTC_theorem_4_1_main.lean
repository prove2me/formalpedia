-- Prove2me | Theorems.Thm_LowAccLTC_theorem_4_1_main
-- name    : LowAccLTC.theorem_4_1_main
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:40:28.979415+00:00
-- url     : https://prove2.me/theorems/b04cc360-0a5d-4a4d-99c0-34c00b6d3607
-- title:
--   Theorem 4.1 (Main theorem) — HA agreement testability under the $j$-test gives $(\varepsilon,\frac x3(1-\alpha-\rho(\alpha)))$-LA local testability
-- statement:
--   Let $\varepsilon,\alpha,\beta\in(0,1)$ with $\alpha\le\frac{2\varepsilon}3$, let $\rho:[0,\alpha]\to[0,1]$ be non-decreasing, and let $j,r>0$ be integers with
--   $$j\ \ge\ \frac{10^{10}\log(1/(\alpha\beta\varepsilon))}{\varepsilon^6},\qquad r\ \ge\ \frac{10^8j^2}{\beta\alpha\varepsilon^3}.$$
--   Let $C=\mathrm{Tan}(X,C_0)$ be an HDX code on a weighted $r$-partite complex $X$, and assume:
--   1. $X$ is an $r^{-2}$-local spectral expander;
--   2. $Y=\mathcal F^jX$ is a $(\lceil6/\varepsilon\rceil,\beta)$-coboundary expander;
--   3. for every face $s$ with $|s|<r$, the local code $C_s$ has distance at least $1-\varepsilon^2/36$;
--   4. $C$ is $(\alpha,\rho)$-agreement testable via the $j$-test.
--
--   Then $C$ is an $(\varepsilon,\varphi)$-LA LTC w.r.t. the vertex test, where
--   $$\varphi(x)=\frac x3\big(1-\alpha-\rho(\alpha)\big).$$
--
--   This is the general framework of the paper; Theorem 5.7 is its application to KMS codes.
--
--   Differences from the source:
--   - reading: C = Tan(X, C₀) a code, with dist(f, C) = min_{c ∈ C} dist(f, c) → the hypothesis that Tan(X, C₀) is nonempty; reason: the paper's distances to a code are minima over the code, so codes are nonempty; if a local code is empty there are no collections {c_s ∈ C_s} and the statement read literally fails (one empty line code makes C empty while almost every vertex code is unaffected)
--   - encoding: a pure r-partite simplicial complex with a positive probability measure on its top faces → PartiteComplex: a finite type of top faces with a vertex map vert t i of colour i (colours Fin r, the paper's colour i is i − 1), injective on top faces, and a positive measure μ summing to 1; reason: faces are the subsets of top faces, so this is exactly a pure weighted r-partite complex
--   - encoding: an alphabet Σ → a type A with [Finite A]; reason: alphabets are finite sets in the paper's setting (codes C ⊆ Σⁿ)
--   - encoding: λ₂ of the link graph's random-walk operator is at most λ → the variational form E_{(u,v)} g(u)g(v) ≤ λ E g² for every g of mean 0 under the link's vertex law; reason: equivalent by self-adjointness and Courant–Fischer
--   - encoding: (ε, φ)-LA LTC with φ : [0,1] → ℝ₊ monotone, ε ∈ (0,1) → IsLALTCVertex: the bare implication x ≥ ε ⇒ 1 − dist(f, C) ≥ φ(x); reason: the side conditions on φ and ε are hypotheses where the paper assumes them; bundling them would make a conclusion with a possibly negative φ false although the paper's claim is the implication
--   - encoding: ρ : [0, α] → [0, 1] non-decreasing → ρ : ℝ → ℝ, MonotoneOn on [0, α], values in [0, 1] on [0, α]; reason: only values on [0, α] are read
--   - reading: log (base not stated) → Real.log (natural logarithm); reason: the paper does not fix the base; ln is the analyst's default and, as a lower-bound hypothesis, weaker than log₂ (ln x < log₂ x for x > 1)
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Theorem 4.1, p.26 (PDF p.29)

import Definitions.Def_LowAccLTC_IsLALTCVertex
import Definitions.Def_LowAccLTC_IsOneSidedLocalSpectral
import Definitions.Def_LowAccLTC_IsFacesCoboundaryExpander

namespace LowAccLTC

/-- **Theorem 4.1** (Main theorem; Ben Yaacov–Dikstein–Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs* (manuscript, sha256 04242e17…), p.26 = PDF p.29).

Let `ε, α, β ∈ (0, 1)` with `α ≤ 2ε/3`, `ρ : [0, α] → [0, 1]` non-decreasing, and integers
`j, r > 0` with `j ≥ 10^10 log(1/(αβε))/ε^6` and `r ≥ 10^8 j²/(βαε³)`. Let `C = Tan(X, C₀)` be a
Tanner code on a weighted `r`-partite complex `X`, and assume: 1. `X` is an `r^{-2}`-local
spectral expander; 2. `F^j X` is a `(⌈6/ε⌉, β)`-coboundary expander; 3. every `C_s` with `|s| < r`
has distance at least `1 - ε²/36`; 4. `C` is `(α, ρ)`-agreement testable via the `j`-test. Then
`C` is an `(ε, φ)`-LA LTC (vertex test) with `φ(x) = (x/3)(1 - α - ρ(α))`. -/
theorem theorem_4_1_main {r : ℕ} {V T A : Type*} [Fintype T] [Finite A]
    (X : PartiteComplex r V T) (C₀ : (u : Finset V) → Set (X.star u → A))
    (ε α β : ℝ) (hε : 0 < ε ∧ ε < 1) (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1)
    (hαε : α ≤ 2 * ε / 3)
    (j : ℕ) (hj : 0 < j) (hr : 0 < r)
    (hj_bound : (10 : ℝ) ^ 10 * Real.log (1 / (α * β * ε)) / ε ^ 6 ≤ j)
    (hr_bound : (10 : ℝ) ^ 8 * (j : ℝ) ^ 2 / (β * α * ε ^ 3) ≤ r)
    (hC : (X.tanner C₀).Nonempty)
    (ρ : ℝ → ℝ) (hρ_mono : MonotoneOn ρ (Set.Icc 0 α))
    (hρ_range : ∀ x ∈ Set.Icc 0 α, 0 ≤ ρ x ∧ ρ x ≤ 1)
    (h1 : X.IsOneSidedLocalSpectral (1 / (r : ℝ) ^ 2))
    (h2 : X.IsFacesCoboundaryExpander j ⌈6 / ε⌉₊ β)
    (h3 : ∀ s, X.IsFace s → s.card < r →
      X.HasDistAtLeast (X.star s) (X.localCode C₀ s) (1 - ε ^ 2 / 36))
    (h4 : X.IsJAgreementTestable C₀ j α ρ) :
    X.IsLALTCVertex C₀ ε (fun x => x / 3 * (1 - α - ρ α)) := by sorry

end LowAccLTC
