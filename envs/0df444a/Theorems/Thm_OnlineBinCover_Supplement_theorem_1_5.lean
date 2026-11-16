-- Prove2me | Theorems.Thm_OnlineBinCover_Supplement_theorem_1_5
-- name    : OnlineBinCover.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:05:57.600263+00:00
-- url     : https://prove2.me/theorems/16444416-4d0d-4474-a816-c18890e9af99
-- title:
--   Theorem 1.5 — uniform IID hardness: $\mathbb E[A(I_n)]\le\mathbb E[\mathrm{OPT}(I_n)]-\Omega(\sqrt{n\log n})$ for arbitrarily large $n$
-- statement:
--   **Uniform IID hardness bound.** There is an absolute constant $c>0$ with the following property. Let $A$ be any possibly randomized online bin covering algorithm that is not told the input length: a probability space $(\Omega,P)$ and a measurable rule assigning item $t$ a bin as a function of the randomness and the sizes of items $0,\dots,t$, the same rule for every input length. Then for every $N$ there is $n\ge N$ with
--   $$\mathbb E[A(I_n)]\ \le\ \mathbb E[\mathrm{OPT}(I_n)]-c\sqrt{n\log n},$$
--   where $I_n$ consists of $n$ independent $\mathrm{Unif}[0,1]$ items.
--
--   An asymptotic ratio of $1$ thus cannot come with an additive gap as small as $O(\log\mathrm{OPT})$: some polynomial dependence on the optimum is unavoidable. The bound holds even if $A$ knows the distribution.
--
--   Differences from the source:
--   - reading: "possibly randomized online bin covering algorithm $A$ that is not told the input length" → a probability space $(\Omega,P)$, $\Omega$ a type, and a rule $\rho(\omega,t,x_0,\dots,x_t)\in\mathbb N$, the same for every length, measurable in $(\omega,x_0,\dots,x_t)$; reason: the paper puts no computational restriction on $A$; measurability makes $\mathbb E[A(I_n)]$ an expectation
--   - reading: $\Omega(\sqrt{n\log n})$ → one constant $c>0$, chosen before the algorithm, and the bound $c\sqrt{n\log n}$; reason: the proof's constant is absolute (Lemmas F.1, F.2 and [CFGR91]); the stronger of the two readings
--   - encoding: "there exist arbitrarily large $n$" → for every $N$ there is $n\ge N$; reason: definition
--   - encoding: $I_n$, $n$ independent $\mathrm{Unif}[0,1]$ items → the product of Lebesgue measure on $[0,1]$; reason: same law
--   - encoding: "even if $A$ knows the distribution" → nothing extra: the distribution is fixed, so the rule may depend on it; reason: already covered
--   - encoding: expectations → lower Lebesgue integrals of nonnegative counts bounded by $n$, as reals; reason: equal to the expectation for the measurable integrands of the statement
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Theorem 1.5, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_OnlineBinCover_Supplement_InfoAlg

namespace OnlineBinCover.Supplement

open MeasureTheory

/-- Theorem 1.5 (Uniform IID hardness bound), p.6 (PDF p.7); proof Section F, pp.40–43.
Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

There is an absolute constant `c > 0` such that for every possibly randomized online bin covering
algorithm `A` that is not told the input length (a probability space `(Ω, P)` and a measurable
rule `ρ` labelling item `t` from `ω` and the sizes of items `0, …, t`, the same rule for every
length), there exist arbitrarily large `n` with
`E[A(I_n)] ≤ E[OPT(I_n)] − c √(n log n)`, where `I_n` consists of `n` independent `Unif[0,1]` items. -/
theorem theorem_1_5 : ∃ c : ℝ, 0 < c ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ρ : Ω → (t : ℕ) → (Fin (t + 1) → ℝ) → ℕ),
      (∀ t : ℕ, Measurable (fun z : Ω × (Fin (t + 1) → ℝ) => ρ z.1 t z.2)) →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        noLenExp P ρ n ≤ unifOptExp n - c * Real.sqrt ((n : ℝ) * Real.log n) := by sorry

end OnlineBinCover.Supplement
