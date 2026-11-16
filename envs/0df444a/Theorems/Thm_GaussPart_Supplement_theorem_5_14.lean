-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_5_14
-- name    : GaussPart.Supplement.theorem_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:11:26.905548+00:00
-- url     : https://prove2.me/theorems/7391b489-3a50-48c0-a5b9-ae76981b67e3
-- title:
--   Theorem 5.14 — SQ lower bound $d^{\Omega(\log(k/\epsilon))}$ for PUI learning intersections of halfspaces
-- statement:
--   **Setting.** Let $k,d\in\mathbb Z_+$, $\epsilon\in(0,1/2)$ and $m^*=\log(k/\epsilon)$. Assume $\max\{k,m^*\}\le d^c$ and $\epsilon\le c/k^3$, where $c>0$ is a sufficiently small universal constant and $d$ is sufficiently large. Let $\mathcal F_k$ be the intersections of at most $k$ halfspaces.
--
--   **Theorem.** Any SQ algorithm that learns $\mathcal F_k$ over distributions that are $(1,1/2)$-smooth with respect to $\mathcal N(0,I_d)$, using SQ access only to the positive conditional distribution, to error $\epsilon(1-\epsilon)/4$ with probability at least $2/3$, requires either
--   $$
--   2^{d^{\Omega(1)}}\ \text{queries}\qquad\text{or a query of tolerance at most}\qquad d^{-\Omega(m^*)} .
--   $$
--
--   With constant smoothness parameters this matches the dimension dependence of Theorem 5.12.
--
--   **Formalization Note** Here $m^*$ is the real number $\log(k/\epsilon)$ (natural logarithm); the constants are existential and chosen first; "learns" quantifies over every target in $\mathcal F_k$, every $(1,1/2)$-smooth distribution giving the target positive mass, and every valid oracle for the positive conditional.
--
--   Differences from the source:
--   - encoding: any SQ algorithm (Definition A.4) that makes no query of tolerance at most τ₀ → every randomized adaptive SQ algorithm of the published SQAlg type whose every query is a measurable [−1,1]-valued function with tolerance > τ₀, against adversarial trajectory-dependent oracles; reason: the published SQ model; states no run reaches can be changed without changing any run
--   - reading: requires 2^{d^{Ω(1)}} queries → on some admissible instance, against some valid oracle, some run makes at least 2^{d^{c₁}} queries with positive probability; reason: worst-case query complexity of a randomized SQ algorithm
--   - reading: learns F_k over (1, 1/2)-smooth distributions using SQ access only to the positive conditional → for every f ∈ F_k, every (1, 1/2)-smooth D′ with D′(f = 1) > 0 and every valid oracle for D′ | {f = 1}, mass ≥ 2/3 on h with Pr_{D′}[h ≠ f] ≤ ϵ(1 − ϵ)/4; reason: the theorem names no lower bound p₊
--   - encoding: sufficiently small c, sufficiently large d, Ω(·) → ∃ c > 0, ∃ d₀, ∃ c₁ c₂ > 0 chosen before d and every parameter; reason: universal constants
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 5.14, p.54 (PDF p.56); informal version Theorem 1.9 (ii), p.5

import Mathlib
import Definitions.Def_PrivLearn_SQSim_SQAlg
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_Supplement_Halfspaces
import Definitions.Def_GaussPart_Supplement_SQ

open MeasureTheory ProbabilityTheory PrivLearn.SQSim

namespace GaussPart

namespace Supplement

/-- **Theorem 5.14** (SQ Lower Bound for PUI Learning Intersections of Halfspaces).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem 5.14, p.54 (PDF p.56);
informal version Theorem 1.9 (ii), p.5.

"There exists a sufficiently small universal constant c > 0 such that the following holds for
sufficiently large d. Let k, d ∈ ℤ₊, ϵ ∈ (0, 1/2) and m∗ = log(k/ϵ). Assume that
max{k, m∗} ≤ d^c, ϵ ≤ c/k³. Then any SQ algorithm that learns F_k over distributions that are
(1, 1/2)-smooth with respect to N(0, I_d), using SQ access only to the positive conditional
distribution, to error ϵ(1 − ϵ)/4 with probability at least 2/3, requires either 2^{d^{Ω(1)}} queries
or a query of tolerance at most d^{−Ω(m∗)}."

**Formalization Note.**
* `c`, the threshold `d₀`, and the constants `c₁, c₂` of the two `Ω(·)` are chosen first. Here `m∗` is
  the real number `log(k/ϵ)` (natural logarithm), not the exponent of Definition 5.2.
* `F_k = IntersectionClass d k`. "Learns" is: for every target `f ∈ F_k` and every `(1, 1/2)`-smooth
  `D′` with `D′(f = 1) > 0` (the theorem names no lower bound `p₊`), against every valid oracle for
  `cond D′ {f = 1}`, the output law gives mass `≥ 2/3` to hypotheses with `Pr_{D′}[h ≠ f] ≤ ϵ(1−ϵ)/4`.
  SQ algorithms, oracles, tolerances and the query count are as in `theorem_5_4`. -/
theorem theorem_5_14 :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (d k : ℕ), d₀ ≤ d → 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      (k : ℝ) ≤ (d : ℝ) ^ c → Real.log (k / ε) ≤ (d : ℝ) ^ c → ε ≤ c / (k : ℝ) ^ 3 →
    ∀ (St : Type) (B : SQAlg (Vec d) (Vec d → ℝ) St),
      TolAbove B ((d : ℝ) ^ (-(c₂ * Real.log (k / ε)))) →
      (∀ f ∈ IntersectionClass d k, ∀ D' : Measure (Vec d), IsProbabilityMeasure D' →
        IsSmooth (stdGaussian (Vec d)) D' 1 (1 / 2) → 0 < D' {x | f x = 1} →
        ∀ O : List St → ℝ, B.IsValidOracle (cond D' {x | f x = 1}) O →
          (2 / 3 : ENNReal) ≤ successMass B O
            {h | D' {x | h x ≠ f x} ≤ ENNReal.ofReal (ε * (1 - ε) / 4)}) →
      ∃ f ∈ IntersectionClass d k, ∃ D' : Measure (Vec d), IsProbabilityMeasure D' ∧
        IsSmooth (stdGaussian (Vec d)) D' 1 (1 / 2) ∧ 0 < D' {x | f x = 1} ∧
        ∃ O : List St → ℝ, B.IsValidOracle (cond D' {x | f x = 1}) O ∧
          MakesManyQueries B O ((2 : ℝ) ^ ((d : ℝ) ^ c₁)) := by sorry

end Supplement

end GaussPart
