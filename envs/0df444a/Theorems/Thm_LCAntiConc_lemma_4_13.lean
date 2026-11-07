-- Prove2me | Theorems.Thm_LCAntiConc_lemma_4_13
-- name    : LCAntiConc.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:17.801743+00:00
-- url     : https://prove2.me/theorems/5aca226e-ecb8-4d7a-a9be-453ace86a66e
-- title:
--   Lemma 4.13 — isotropic $\kappa$-strongly log-concave laws are $\delta$-strengthened anti-concentrated at degree $O(\kappa^{-1}\delta^{-2})$
-- statement:
--   There are absolute constants $\delta_0,A,C>0$ such that for every $0<\delta<\delta_0$ and every $0<\kappa\le1$ there are a polynomial $q$, the square of an even polynomial, and an integer $m\le C\kappa^{-1}\delta^{-2}$ such that every isotropic $\kappa$-strongly log-concave $X\in\mathbb R^d$, in every dimension $d$, is $\delta$-strengthened anti-concentrated at degree $m$ (Definition 4.1, with constant $A$), witnessed by $q$.
--
--   The polynomial $q$ depends only on $\delta$ and $\kappa$, and the constants of Definition 4.1 do not depend on $\kappa$.
--
--   Differences from the source:
--   - reading: "δ smaller than a small enough absolute constant" → ∃ δ₀ > 0, ∀ δ ∈ (0, δ₀); reason: the usual meaning of the phrase
--   - reading: each O(·) (the implicit constants of Definition 4.1 and m ≤ O(κ⁻¹δ⁻²)) → one universal constant C, quantified first; reason: p.27: the constants hidden in the O(·) notation are universal; one constant for several O's is equivalent (take the maximum)
--   - reading: "q depends only on δ and κ, but not on X" → q and m chosen after δ and κ and before d and the law; reason: the literal content of the sentence
--   - reading: "degree-m polynomial" in Definition 4.1 → deg q ≤ m; reason: Lemmas 4.12–4.13 say "for some m ≤ …" and Theorem 4.2 uses m only through D = O(m + δ^{-30}); ≤ is the reading under which the chain fits
--   - encoding: random vector X ∈ ℝ^d → its law μ, a probability measure on EuclideanSpace ℝ (Fin d); reason: Euclidean norm and inner product; same instances
--   - encoding: density e^{-V}, V : ℝ^d → ℝ ∪ {+∞} convex → density f = e^{-V} ≥ 0 with f((1-θ)x+θy) ≥ f(x)^{1-θ} f(y)^θ (resp. for f(x)e^{κ‖x‖²/2}); reason: convexity of V = -log f with values in ℝ ∪ {+∞}; same class
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.13, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_LCAntiConc_IsIsotropic
import Definitions.Def_LCAntiConc_IsStronglyLogConcave
import Definitions.Def_LCAntiConc_IsStrengthenedAC

namespace LCAntiConc

open MeasureTheory

/-- **Lemma 4.13** (Strengthened Anti-Concentration of Strongly Log-Concave Distributions). Let
`0 < δ` be smaller than a small enough absolute constant and `0 < κ ≤ 1`. Every isotropic
`κ`-strongly log-concave `X ∈ ℝ^d` is `δ`-strengthened anti-concentrated at degree `m`
(Definition 4.1) for some `m ≤ O(κ⁻¹δ⁻²)`. The polynomial `q` is the square of an even polynomial
and depends only on `δ` and `κ`, but not on `X`, and the constants implicit in Definition 4.1 do
not depend on `κ`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.13, p.29 (PDF p.31).

**Formalization Note** `δ₀`, the constant `A` of Definition 4.1 and the constant `C` of
`m ≤ Cκ⁻¹δ⁻²` are absolute and come before `δ` and `κ`; `q` and `m` come before `d` and the
law. -/
theorem lemma_4_13 :
    ∃ δ₀ > 0, ∃ A > 0, ∃ C > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ κ : ℝ, 0 < κ → κ ≤ 1 →
      ∃ q : Polynomial ℝ, (∃ p : Polynomial ℝ, (∀ t, p.eval (-t) = p.eval t) ∧ q = p ^ 2) ∧
      ∃ m : ℕ, (m : ℝ) ≤ C * κ⁻¹ * δ ^ (-2 : ℤ) ∧
        ∀ (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))),
          IsIsotropic μ → IsStronglyLogConcave κ μ → IsStrengthenedAC μ δ m A q := by sorry

end LCAntiConc
