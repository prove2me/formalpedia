-- Prove2me | Theorems.Thm_KingRockAsymp_Distribution_proposition_A1
-- name    : KingRockAsymp.Distribution.proposition_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:59.786248+00:00
-- url     : https://prove2.me/theorems/16902c66-2efd-406d-980e-ec80f155771d
-- title:
--   Proposition A1 — the integrand is a Borel measurable map into $C_m(U)$
-- statement:
--   Let $U \subseteq \mathbb R^n$ be compact, $(S,\mathcal S)$ a measurable space, and $f : U \times S \to \mathbb R^m$ satisfy P.1–P.4: continuity in $x$ and measurability in $s$; i.i.d. samples $s_i$; a finite second moment at one point of $U$; and a Lipschitz bound in $x$ with a square-integrable modulus. Then the map
--   $$s \mapsto f(\cdot, s), \qquad S \to C_m(U),$$
--   is Borel measurable, where $C_m(U)$ is the Banach space of continuous $\mathbb R^m$-valued functions on $U$ with the sup norm and its Borel $\sigma$-algebra.
--
--   This makes $s \mapsto f(\cdot,s)$ a random element of a separable Banach space, the setting of the central limit theorem A3.
--
--   **Formalization Note** All of P.1–P.4 are hypotheses as printed, although the proof of measurability uses P.1. Continuity in $x$ is built into the type `S → C(↥U, Rn m)`; measurability in $s$ is a hypothesis. Compactness of $U$ is the instance `CompactSpace ↥U`.
-- source:
--   King & Rockafellar, Asymptotic Theory for Solutions in Statistical Estimation and Stochastic Programming, Math. Oper. Res. 18(1) (1993), Appendix, Proposition A1, p. 16 (authors' manuscript pagination)

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic

namespace KingRockAsymp.Distribution

open Set Filter Topology Metric MeasureTheory ProbabilityTheory

theorem proposition_A1 {n m : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (Rn n)) [CompactSpace ↥U] (f : S → C(↥U, Rn m))
    (hmeas : ∀ x : ↥U, Measurable (fun σ => f σ x))
    (s : ℕ → Ω → S) (hs : ∀ i, Measurable (s i))
    (hindep : iIndepFun s P) (hident : ∀ i, IdentDistrib (s i) (s 0) P P)
    (hP3 : ∃ x : ↥U, MemLp (fun ω => f (s 0 ω) x) 2 P)
    (hP4 : ∃ a : S → ℝ, MemLp (fun ω => a (s 0 ω)) 2 P ∧
      ∀ σ : S, ∀ x₁ x₂ : ↥U, ‖f σ x₁ - f σ x₂‖ ≤ a σ * ‖(x₁ : Rn n) - x₂‖) :
    Measurable f := by sorry

end KingRockAsymp.Distribution
