-- Prove2me | Theorems.Thm_LCAntiConc_lemma_4_12
-- name    : LCAntiConc.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:30.598868+00:00
-- url     : https://prove2.me/theorems/d407fbd1-a381-417c-864c-ba8e2979dd86
-- title:
--   Lemma 4.12 — isotropic log-concave laws are $\delta$-strengthened anti-concentrated at degree $\exp(O(1/\delta))$
-- statement:
--   There are absolute constants $\delta_0,A,C>0$ such that for every $0<\delta<\delta_0$ there are a polynomial $q$, the square of an even polynomial, and an integer $m\le\exp(C/\delta)$ such that every isotropic log-concave $X\in\mathbb R^d$, in every dimension $d$, is $\delta$-strengthened anti-concentrated at degree $m$ (Definition 4.1, with constant $A$), witnessed by $q$.
--
--   The polynomial $q$ depends only on $\delta$, not on $X$ or $d$.
--
--   Differences from the source:
--   - reading: "δ smaller than a small enough absolute constant" → ∃ δ₀ > 0, ∀ δ ∈ (0, δ₀); reason: the usual meaning of the phrase
--   - reading: each O(·) (the implicit constants of Definition 4.1 and m ≤ exp(O(1/δ))) → one universal constant C, quantified first; reason: p.27: the constants hidden in the O(·) notation are universal; one constant for several O's is equivalent (take the maximum)
--   - reading: "q depends only on δ, but not on X" → q and m chosen after δ and before d and the law; reason: the literal content of the sentence; m can be taken as deg q
--   - reading: "degree-m polynomial" in Definition 4.1 → deg q ≤ m; reason: Lemmas 4.12–4.13 say "for some m ≤ …" and Theorem 4.2 uses m only through D = O(m + δ^{-30}); ≤ is the reading under which the chain fits
--   - encoding: random vector X ∈ ℝ^d → its law μ, a probability measure on EuclideanSpace ℝ (Fin d); reason: Euclidean norm and inner product; same instances
--   - encoding: density e^{-V}, V : ℝ^d → ℝ ∪ {+∞} convex → density f = e^{-V} ≥ 0 with f((1-θ)x+θy) ≥ f(x)^{1-θ} f(y)^θ (resp. for f(x)e^{κ‖x‖²/2}); reason: convexity of V = -log f with values in ℝ ∪ {+∞}; same class
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.12, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_LCAntiConc_IsIsotropic
import Definitions.Def_LCAntiConc_IsLogConcave
import Definitions.Def_LCAntiConc_IsStrengthenedAC

namespace LCAntiConc

open MeasureTheory

/-- **Lemma 4.12** (Strengthened Anti-Concentration of Log-Concave Distributions). Let `0 < δ` be
smaller than a small enough absolute constant. Every isotropic log-concave `X ∈ ℝ^d` is
`δ`-strengthened anti-concentrated at degree `m` (Definition 4.1) for some `m ≤ exp(O(1/δ))`. The
polynomial `q` is the square of an even polynomial and depends only on `δ`, but not on `X`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.12, p.28 (PDF p.30).

**Formalization Note** The constant `A` of Definition 4.1 and the constant `C` of
`m ≤ exp(C/δ)` are absolute and come first; `q` and `m` are chosen from `δ` alone, before `d`
and the law. -/
theorem lemma_4_12 :
    ∃ δ₀ > 0, ∃ A > 0, ∃ C > 0, ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ q : Polynomial ℝ, (∃ p : Polynomial ℝ, (∀ t, p.eval (-t) = p.eval t) ∧ q = p ^ 2) ∧
      ∃ m : ℕ, (m : ℝ) ≤ Real.exp (C / δ) ∧
        ∀ (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))),
          IsIsotropic μ → IsLogConcave μ → IsStrengthenedAC μ δ m A q := by sorry

end LCAntiConc
