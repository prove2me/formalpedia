-- Prove2me | Theorems.Thm_LocalLLL_Main_section_3_3_recursion
-- name    : LocalLLL.Main.section_3_3_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:16.29457+00:00
-- url     : https://prove2.me/theorems/c70223e2-5f6a-4284-ba14-669a391447c8
-- title:
--   §3.3 — closed forms, first terminal level and round recurrence
-- statement:
--   For a finite graph, the recurrence $G_0=G$, $G_{i+1}=G_i^{23}$ has closed form $G_i=G^{23^i}$. The real recurrences $\lambda_0=1000$, $\lambda_{i+1}=\lambda_i^2/700$ and $d_0=d$, $d_{i+1}=d_i^{23}$ have closed forms
--
--   $$\lambda_i=700(10/7)^{2^i},\qquad d_i=d^{23^i}.$$
--
--   For every $a>0$, natural $B$ and nonnegative constants $A',K$, a constant $c>0$ depending only on $a$, and then $A>0$, work uniformly over every $n\ge1$ and real $d\ge3$: the first index $L$ with $\lambda_L\log d_L\ge a\log n$ exists, satisfies $L\le c(1+\log\ell(n))$, and every real cost sequence with $T_L\le K$, $T_i\le23T_{i+1}+b$ for $i<L$ and $b\le A'\ell(n)^B$ satisfies
--
--   $$T_0\le A\ell(n)^{B+5}.$$
--
--   This makes the asymptotic iteration and communication bounds explicit. The extra exponent 5 is allowed by $\log_2 23<5$; no integer-valued assumption is made on the exponent sequence.
--
--   Differences from the source:
--   - encoding: asymptotic iteration and round bounds → explicit positive constants uniform in n and d, exponent B+5, and log log(n+16); reason: the closed forms give 23^L=O((log log(n+16))^(log₂23)), and log₂23<5; padding handles n=1
--   - generalization: degree sequence from an integer d≥d_min≥3 → real d for the algebraic closed form, and real d≥3 for the terminal and round estimates; reason: the arithmetic and logarithmic estimates hold for every real d≥3 and specialize to all degree bounds
--   - encoding: unspecified logarithm bases → natural logarithms; reason: changes of base are absorbed into a and the existential multiplicative constants
--   - encoding: the graph recurrence G_0=G, G_(i+1)=G_i^23 and its closed form G_i=G^(23^i) → a sequence H of finite simple graphs with H 0 = G and H (i+1) = graphPower (H i) 23, concluding H i = graphPower G (23^i); reason: the loopless graph-power definition uses extended distance and includes disconnected graphs; the statement retains the graph clause alongside both scalar closed forms
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), §3.3 recursion paragraph, p. 7 (PDF 8); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Repair

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalLLL.Main

/-- §3.3 recurrences, printed p. 7. All costs are measured in their own level's graph. -/
theorem section_3_3_recursion :
    (∀ lam : ℕ → ℝ, lam 0 = 1000 → (∀ i, lam (i + 1) = lam i ^ 2 / 700) →
      ∀ i, lam i = 700 * (10 / 7 : ℝ) ^ (2 ^ i : ℕ)) ∧
    (∀ delta : ℕ → ℝ, ∀ d : ℝ, delta 0 = d →
      (∀ i, delta (i + 1) = delta i ^ (23 : ℕ)) →
      ∀ i, delta i = d ^ (23 ^ i : ℕ)) ∧
    (∀ (V : Type) [Fintype V] (G : SimpleGraph V) (H : ℕ → SimpleGraph V),
      H 0 = G → (∀ i, H (i + 1) = graphPower (H i) 23) →
      ∀ i, H i = graphPower G (23 ^ i)) ∧
    (∀ a : ℝ, 0 < a → ∃ c : ℝ, 0 < c ∧
      ∀ B : ℕ, ∀ A' K : ℝ, 0 ≤ A' → 0 ≤ K →
      ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, 1 ≤ n → ∀ d : ℝ, 3 ≤ d →
      ∃ L : ℕ,
        (700 * (10 / 7 : ℝ) ^ (2 ^ L : ℕ)) * Real.log (d ^ (23 ^ L : ℕ)) ≥ a * Real.log (n : ℝ) ∧
        (∀ i < L, (700 * (10 / 7 : ℝ) ^ (2 ^ i : ℕ)) * Real.log (d ^ (23 ^ i : ℕ)) <
          a * Real.log (n : ℝ)) ∧
        (L : ℝ) ≤ c * (1 + Real.log (loglog n)) ∧
        (∀ (T : ℕ → ℝ) (b : ℝ), b ≤ A' * loglog n ^ B →
          T L ≤ K → (∀ i < L, T i ≤ 23 * T (i + 1) + b) →
          T 0 ≤ A * loglog n ^ (B + 5))) := by sorry

end LocalLLL.Main
