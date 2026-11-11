-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_lemma_6_10
-- name    : NonMarkovColorings.Main.lemma_6_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:08:44.196196+00:00
-- url     : https://prove2.me/theorems/873af938-f3b6-443d-ac3b-bd4a001ae045
-- title:
--   Lemma 6.10 — missing colors of independent $[k]$-valued variables: $\mathbb E|A|\ge k((1-p)/e)^{d/k}$ and two-sided concentration
-- statement:
--   Let $k,d\ge1$ and let $\xi_1,\dots,\xi_d$ be independent random variables with values in $[k]$. Let $p=\max_{1\le j\le d}\max_{a\in[k]}\mathbb P[\xi_j=a]$ and let $A=[k]\setminus\{\xi_1,\dots,\xi_d\}$ be the set of missing colors. Then
--   $$\mathbb E|A|\ \ge\ k\Big(\frac{1-p}{e}\Big)^{d/k},\qquad \mathbb P\big[\,\big||A|-\mathbb E|A|\big|\ge a\big]\le 2e^{-a^2/(2k)}\quad(a\ge 0).$$
--   This is the Dyer–Frieze bound on available colors, extended by Hayes to independent (not identically distributed) neighbours; it is the elementary input of the local-uniformity analysis of §6.
--
--   **Formalization Note.** $\xi_j:\Omega\to$ `Fin k`, measurable and `iIndepFun` under a probability measure; $p$ is the supremum over the finite nonempty index sets (a maximum); $(\cdot)^{d/k}$ is a real power.
--
--   Differences from the source:
--   - encoding: colors [k] = {1, …, k} → Fin k = {0, …, k−1}; reason: Lean convention; a relabeling of colors, same instances
--   - encoding: p = max_j max_a P[ξ_j = a] → ⨆ j, ⨆ a, P.real {ξ j = a} over Fin d, Fin k; reason: a supremum over a finite nonempty index set of reals is the maximum
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 43, Lemma 6.10

import Mathlib

namespace NonMarkovColorings.Main

/-- Lemma 6.10 (see [Hay13, Lemma 23]). For independent `ξ_1, …, ξ_d` with values in `[k]`
(`Fin k`), `p = max_j max_a P[ξ_j = a]` and `A = [k] \ {ξ_1, …, ξ_d}`:
`E|A| ≥ k ((1 − p)/e)^{d/k}`, and `P[||A| − E|A|| ≥ a] ≤ 2 e^{−a²/(2k)}` for every `a ≥ 0`. -/
theorem lemma_6_10 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (ξ : Fin d → Ω → Fin k) (hξ : ∀ j, Measurable (ξ j))
    (hind : ProbabilityTheory.iIndepFun ξ P) :
    let p : ℝ := ⨆ j : Fin d, ⨆ a : Fin k, P.real {ω | ξ j ω = a}
    let A : Ω → Finset (Fin k) := fun ω => Finset.univ \ Finset.univ.image fun j => ξ j ω
    (k : ℝ) * ((1 - p) / Real.exp 1) ^ ((d : ℝ) / k) ≤ ∫ ω, ((A ω).card : ℝ) ∂P ∧
      ∀ a : ℝ, 0 ≤ a →
        P.real {ω | a ≤ |((A ω).card : ℝ) - ∫ ω', ((A ω').card : ℝ) ∂P|} ≤
          2 * Real.exp (-(a ^ 2) / (2 * k)) := by sorry

end NonMarkovColorings.Main
