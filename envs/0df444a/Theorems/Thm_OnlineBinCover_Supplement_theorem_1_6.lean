-- Prove2me | Theorems.Thm_OnlineBinCover_Supplement_theorem_1_6
-- name    : OnlineBinCover.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:06:44.76755+00:00
-- url     : https://prove2.me/theorems/337d6be4-6a89-4144-a835-95561b2d97d3
-- title:
--   Theorem 1.6 — $K$ moments do not suffice: $\mathbb E[A(X)]\le(1-c/K)\,\mathbb E[\mathrm{OPT}(X)]$ on instances with arbitrarily large optimum
-- statement:
--   **A limitation of moment information.** There is an absolute constant $c>0$ such that for every fixed integer $K\ge1$ and every possibly randomized online algorithm $A$ given only the first $K$ moments of each distribution and no samples (a probability space $(\Omega,P)$ and a rule measurable in the randomness and the sizes seen so far), the following holds: for every $M$ there are $n$ and independent distributions $D_1,\dots,D_n$ on $(0,1]$, the items arriving in index order, with $\mathbb E[\mathrm{OPT}(X)]\ge M$ and
--   $$\mathbb E[A(X)]\ \le\ \Big(1-\frac cK\Big)\,\mathbb E[\mathrm{OPT}(X)].$$
--
--   Together with Theorem 1.4, this separates sample access from access to finitely many exact moments.
--
--   Differences from the source:
--   - reading: "possibly randomized online algorithm $A$, given only the first $K$ moments of each distribution and no samples" → a probability space $(\Omega,P)$, $\Omega$ a type, and a rule receiving $n$, the table $\int x^j\,dD_i$ ($1\le j\le K$, $i\le n$), the time $t$ and the sizes of items $0,\dots,t$, measurable in the randomness and the sizes; reason: no computational restriction; the moment table of the $n$ distributions already reveals $n$; measurability makes $\mathbb E[A(X)]$ an expectation
--   - encoding: "instances with arbitrarily large $\mathbb E[\mathrm{OPT}(X)]$" → for every $M$ there are $n$ and $D_1,\dots,D_n$ with $\mathbb E[\mathrm{OPT}(X)]\ge M$; reason: definition; the instance is chosen after the algorithm, as in Section G
--   - encoding: an instance of the prophet model → $n$ probability measures on $\mathbb R$ with $D_i((0,1]^c)=0$, items arriving in index order; reason: an adversarial order is absorbed by relabelling the distributions
--   - encoding: expectations → lower Lebesgue integrals of nonnegative counts bounded by $n$, as reals; reason: equal to the expectation for the measurable integrands of the statement
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Theorem 1.6 (restated), p.43 (PDF p.44); stated p.6 (PDF p.7)

import Mathlib
import Definitions.Def_OnlineBinCover_Supplement_InfoAlg

namespace OnlineBinCover.Supplement

open MeasureTheory

/-- Theorem 1.6 (A limitation of moment information, restated), p.43 (PDF p.44); stated p.6;
proof Section G, pp.43–46.
Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

There is an absolute constant `c > 0` such that, for every fixed integer `K ≥ 1` and every
possibly randomized online algorithm `A` given only `n` and the first `K` moments of each
distribution and no samples (a probability space `(Ω, P)` and a rule `ρ`, measurable in the
randomness and the sizes seen so far), there are instances — independent distributions
`D_1, …, D_n` on `(0,1]`, items arriving in index order — with arbitrarily large `E[OPT(X)]`
for which `E[A(X)] ≤ (1 − c/K) E[OPT(X)]`. -/
theorem theorem_1_6 : ∃ c : ℝ, 0 < c ∧
    ∀ K : ℕ, 1 ≤ K →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ρ : Ω → (n : ℕ) → (Fin n → Fin K → ℝ) → (t : Fin n) → (Fin (t.val + 1) → ℝ) → ℕ),
      (∀ (n : ℕ) (mom : Fin n → Fin K → ℝ) (t : Fin n),
        Measurable (fun z : Ω × (Fin (t.val + 1) → ℝ) => ρ z.1 n mom t z.2)) →
      ∀ M : ℝ, ∃ (n : ℕ) (D : Fin n → ProbabilityMeasure ℝ),
        (∀ i, (D i : Measure ℝ) (Set.Ioc 0 1)ᶜ = 0) ∧
        M ≤ optExp D ∧
        momExp P ρ D ≤ (1 - c / (K : ℝ)) * optExp D := by sorry

end OnlineBinCover.Supplement
