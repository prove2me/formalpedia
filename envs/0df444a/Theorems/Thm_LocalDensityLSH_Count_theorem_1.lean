-- Prove2me | Theorems.Thm_LocalDensityLSH_Count_theorem_1
-- name    : LocalDensityLSH.Count.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:57.4994+00:00
-- url     : https://prove2.me/theorems/52920d83-25c4-455b-b21d-d060ba8d748b
-- title:
--   Theorem 1, p. 6 — LSH Count is a (1 ± ε)-approximation to |𝒜q| with probability 1 − δ (with the constants of its proof)
-- statement:
--   Let $v_1,\dots,v_n$ and $q$ be unit vectors in $\mathbb R^d$, let $\mathcal A$ be a range of angles, and let $\mathcal A_q=\{i:\theta_{qv_i}\in\mathcal A\}$ be nonempty. Fix a hash law $\mu$ on tables and a Hamming range $\mathcal I$ such that $p(x)>0$ for every $x\in\mathcal A_q$, and write $p_{\min}=\min_{x\in\mathcal A_q}p(x)$ and $\mathbb E(C_q(\mathcal I))=\sum_{y}p(y)$. Let $\varepsilon>0$ and $0<\delta<1$, and run $M$ independent LSH Count estimators, each with $K$ tables and $S$ samples, where
--   $$K\ge\frac{8}{\varepsilon^2p_{\min}},\qquad S\ge\frac{8(1+\varepsilon^2)\,\mathbb E(C_q(\mathcal I))}{\varepsilon^2|\mathcal A_q|\,p_{\min}},\qquad M\ge 11\ln\frac1\delta .$$
--   Then the median $\widehat N$ of the $M$ estimates is a $(1\pm\varepsilon)$-approximation to $|\mathcal A_q|$ with probability at least $1-\delta$:
--   $$\mathbb P\Big(\big|\widehat N-|\mathcal A_q|\big|\le\varepsilon|\mathcal A_q|\Big)\ \ge\ 1-\delta .$$
--
--   In total the estimator uses $MK=O\big(\tfrac{1}{\varepsilon^2p_{\min}}\log\tfrac1\delta\big)$ tables and $MS=O\big(\tfrac{\mathbb E(C_q(\mathcal I))}{\varepsilon^2|\mathcal A_q|p_{\min}}\log\tfrac1\delta\big)$ samples, which is the paper's statement. The sample complexity replaces the ratio $n/|\mathcal A_q|$ of naive random sampling by $\mathbb E(C_q(\mathcal I))/(|\mathcal A_q|\,p_{\min})$.
--
--   **Formalization Note.** Theorem 1 is printed with $O(\cdot)$ and unspecified constants; here the constants are those of its proof: $K$ from Lemma 3, $S$ from Lemma 6, and $M$ from "it suffices to have $e^{-M/11}\le\delta$" (p. 16). The $S$ bound carries the factor $8$ that the printed proof of Lemma 6 drops (see that item). "$(1\pm\varepsilon)$-approximation" is read as $|\widehat N-|\mathcal A_q||\le\varepsilon|\mathcal A_q|$. Added hypotheses, implicit in the paper: $\mathcal A_q\neq\emptyset$ and $p>0$ on $\mathcal A_q$ (for $\min$ and the weights $1/p(x)$), $\varepsilon>0$, $0<\delta<1$. The hash law is arbitrary, which generalizes the paper's random-hyperplane LSH. The median is the lower median.
-- source:
--   Wu, Charikar & Natchu, Local Density Estimation in High Dimensions, arXiv:1809.07471v1, Theorem 1, p. 6; proof §4–§5, pp. 9–17 (Lemmas 1–6, median of means pp. 15–16, conclusion p. 17)

import Mathlib
import Definitions.Def_LocalDensityLSH_Count_Model
import Definitions.Def_LocalDensityLSH_Count_Estimator

namespace LocalDensityLSH.Count

open MeasureTheory ProbabilityTheory

/-- Theorem 1 (LSH Count), p. 6, with the constants of its proof: with `K ≥ 8/(ε² p_min)` tables
and `S ≥ 8(1 + ε²) 𝔼(C_q(ℐ)) / (ε²|𝒜q| p_min)` samples per estimator, and `M ≥ 11 ln(1/δ)`
independent estimators, the median estimate is within `ε|𝒜q|` of `|𝒜q|` with probability at least
`1 − δ`. -/
theorem theorem_1 {n d t K S M : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) (hv : ∀ i, ‖v i‖ = 1)
    (q : EuclideanSpace ℝ (Fin d)) (hq : ‖q‖ = 1) (A : Set ℝ) (I : Finset ℕ)
    (μ : Measure (Table n t)) [IsProbabilityMeasure μ]
    (hA : (Aq v q A).Nonempty) (hp : ∀ i ∈ Aq v q A, 0 < p μ I i)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hK : 8 / (ε ^ 2 * pmin μ I hA) ≤ (K : ℝ))
    (hS : 8 * (1 + ε ^ 2) * EC μ I / (ε ^ 2 * ((Aq v q A).card : ℝ) * pmin μ I hA) ≤ (S : ℝ))
    (hM : 11 * Real.log (1 / δ) ≤ (M : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Fin M → Fin K → Ω → Table n t) (X : Fin M → Fin S → Ω → Fin K × Fin n)
    (hrun : IsRun μ I P T X) :
    1 - δ ≤ P.real {ω |
      |median (fun m => estimate μ I (Aq v q A) (fun k => T m k ω) (fun s => X m s ω))
          - (Aq v q A).card| ≤ ε * (Aq v q A).card} := by sorry

end LocalDensityLSH.Count
