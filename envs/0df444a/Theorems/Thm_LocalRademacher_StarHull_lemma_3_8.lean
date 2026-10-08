-- Prove2me | Theorems.Thm_LocalRademacher_StarHull_lemma_3_8
-- name    : LocalRademacher.StarHull.lemma_3_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:28:32.947984+00:00
-- url     : https://prove2.me/theorems/2e019c63-deb8-461e-bf81-7cfc70ed8f0f
-- title:
--   Lemma 3.8 (third and fourth claims, third corrected), pp. 14–15 — from Ṽᵣ± ≤ r/(BK) to bounds on Pf and Pₙf for all f ∈ F
-- statement:
--   Fix a sample $X_1, \dots, X_n$, and write $P_n f = \frac1n \sum_{i=1}^n f(X_i)$ and $Pf = \mathbb E f(X)$. Let $\mathcal F$ be a class of functions and $T$ a functional with
--   $$
--   0 \le T(f) \le B\, Pf \qquad (f \in \mathcal F)
--   $$
--   for a constant $B > 0$. Fix $K > 1$ and $r > 0$, and let $\tilde{\mathcal G}_r = \{ r f / (T(f) \vee r) : f \in \mathcal F\}$.
--
--   1. If $Pg - P_n g \le r/(BK)$ for every $g \in \tilde{\mathcal G}_r$, then every $f \in \mathcal F$ satisfies
--   $$
--   Pf \le \max\Big\{ P_n f,\ \frac{K}{K-1} P_n f \Big\} + \frac{r}{BK}.
--   $$
--   2. If $P_n g - P g \le r/(BK)$ for every $g \in \tilde{\mathcal G}_r$, then every $f \in \mathcal F$ satisfies
--   $$
--   P_n f \le \frac{K+1}{K} P f + \frac{r}{BK}.
--   $$
--
--   The hypotheses say $\tilde V_r^+ = \sup_{g \in \tilde{\mathcal G}_r} (Pg - P_n g) \le r/(BK)$ and $\tilde V_r^- \le r/(BK)$. The lemma converts a uniform bound on the rescaled class into the error bounds of Theorem 3.3 on the original class.
--
--   **Formalization Note** The page prints $\frac{K}{K-1} P_n f$ in the first claim. For $P_n f < 0$ the argument gives only $P_n f$, and the printed claim fails: with $\mathcal X = \{0,1\}$, $P\{1\} = 0.6$, $f(0) = -1$, $f(1) = 1$ (so $Pf = 0.2$), $T(f) = 0.96$, $B = 5$, $K = 2$, $r = 12$ and the one-point sample $(0)$, one has $\tilde{\mathcal G}_r = \{f\}$ and $\tilde V_r^+ = 1.2 = r/(BK)$, while the printed claim asserts $0.2 \le -0.8$. The maximum is stated instead; it coincides with the print when $P_n f \ge 0$. The second claim is as printed. The suprema $\tilde V_r^\pm$ are written as "for every $g$" bounds. The paper's $\lambda$ plays no role in these two claims and is omitted; the lemma's first two claims (about $V_r^\pm$) are not stated.
-- source:
--   Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, Lemma 3.8, third and fourth claims, pp. 14–15 (notation G̃ᵣ, Ṽᵣ± on p. 14)

import Mathlib
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_LocalRademacher_StarHull_Classes

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized

namespace LocalRademacher.StarHull

/-- **Lemma 3.8, third and fourth claims** (pp. 14–15; third claim corrected). Fix a sample
`s = (X₁, …, Xₙ)`, `B > 0`, `K > 1`, `r > 0`, and a functional `T` with `0 ≤ T(f) ≤ B Pf` for
every `f ∈ F`. With `G̃ᵣ = {r f / (T(f) ∨ r) : f ∈ F}`:
1. if `Pg − Pₙg ≤ r/(BK)` for every `g ∈ G̃ᵣ` (that is, `Ṽᵣ⁺ ≤ r/(BK)`), then every `f ∈ F`
   satisfies `Pf ≤ max{Pₙf, K/(K−1) Pₙf} + r/(BK)`;
2. if `Pₙg − Pg ≤ r/(BK)` for every `g ∈ G̃ᵣ` (that is, `Ṽᵣ⁻ ≤ r/(BK)`), then every `f ∈ F`
   satisfies `Pₙf ≤ (K+1)/K Pf + r/(BK)`.
The page prints `K/(K−1) Pₙf` in the first claim; for `Pₙf < 0` the proof gives only `Pₙf`, and
the printed claim fails, so the maximum is stated (it equals the print when `Pₙf ≥ 0`). -/
theorem lemma_3_8 {X : Type*} [MeasurableSpace X] (P : Measure X) {n : ℕ} (s : Fin n → X)
    (F : Set (X → ℝ)) (T : (X → ℝ) → ℝ) (B K r : ℝ) (hB : 0 < B) (hK : 1 < K) (hr : 0 < r)
    (hT0 : ∀ f ∈ F, 0 ≤ T f) (hTB : ∀ f ∈ F, T f ≤ B * ∫ y, f y ∂P) :
    ((∀ g ∈ tildeG F T r, (∫ y, g y ∂P) - empMean s g ≤ r / (B * K)) →
        ∀ f ∈ F, ∫ y, f y ∂P ≤ max (empMean s f) (K / (K - 1) * empMean s f) + r / (B * K)) ∧
      ((∀ g ∈ tildeG F T r, empMean s g - ∫ y, g y ∂P ≤ r / (B * K)) →
        ∀ f ∈ F, empMean s f ≤ (K + 1) / K * ∫ y, f y ∂P + r / (B * K)) := by sorry

end LocalRademacher.StarHull
