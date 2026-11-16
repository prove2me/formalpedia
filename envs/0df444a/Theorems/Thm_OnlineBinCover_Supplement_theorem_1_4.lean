-- Prove2me | Theorems.Thm_OnlineBinCover_Supplement_theorem_1_4
-- name    : OnlineBinCover.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:04:52.724359+00:00
-- url     : https://prove2.me/theorems/2b57deaf-56e9-4b7f-bc01-a8cd6ce21177
-- title:
--   Theorem 1.4 — single-sample prophet: $\mathbb E[A_{sp}(X;S)]\ge\mathbb E[\mathrm{OPT}(X)]-o(\mathbb E[\mathrm{OPT}(X)])$
-- statement:
--   **Single-sample prophet bin covering.** There is a randomized polynomial-time online algorithm $A_{sp}$: one program $P$ of the exact real RAM with fair coins, and constants $C,e$, such that:
--
--   1. **(polynomial time)** on every coin tape, for every $n$, all samples and online sizes in $(0,1]$ and every arrival order, every per-item run halts and the total work is at most $C(n+1)^e$;
--   2. **(guarantee)** there is a function $f$ with $f(\mu)/\mu\to0$ as $\mu\to\infty$ such that for every $n$, every collection of distributions $D_1,\dots,D_n$ on $(0,1]$ and every arrival order $\tau$ fixed before the draws,
--   $$\mathbb E[A_{sp}(X;S)]\ \ge\ \mathbb E[\mathrm{OPT}(X)]-f\big(\mathbb E[\mathrm{OPT}(X)]\big),$$
--   where the algorithm receives one labelled sample $S_i\sim D_i$ per distribution, the online sizes are $X_i\sim D_i$, samples, sizes and coins are independent, and only the bins covered by the online items count.
--
--   One sample per distribution therefore suffices for asymptotic competitive ratio $1$ in the prophet model.
--
--   Differences from the source:
--   - reading: "randomized polynomial-time online algorithm" → a program of `PNormReg.Machine` with rational literals, coins and no power instruction, one coin tape for the whole run; on every coin tape, every per-item run halted and total work $\le C(n+1)^e$ for samples and sizes in $(0,1]$; reason: the paper names no machine; worst-case time
--   - reading: the single-sample model (labelled samples; items arrive with their labels) → initial memory $n$ and $S_0,\dots,S_{n-1}$; at each arrival the size and the label of the item are written; only online items count; reason: Algorithm 1 uses the labels of the samples and of the arriving items
--   - reading: "every arrival order fixed before the draws" → for every permutation $\tau$, quantified outside the expectation; reason: the order does not depend on $S$ or $X$
--   - encoding: $o(\mathbb E[\mathrm{OPT}(X)])$ → one function $f:\mathbb R\to\mathbb R$ with $f(\mu)/\mu\to0$ as $\mu\to\infty$, chosen before $n$, $D$ and $\tau$; reason: the meaning of a uniform $o(\cdot)$
--   - encoding: independent distributions $D_1,\dots,D_n$ on $(0,1]$ → probability measures on $\mathbb R$ with $D_i((0,1]^c)=0$; reason: same distributions
--   - encoding: expectations → lower Lebesgue integrals of nonnegative counts bounded by $n$, as reals; reason: equal to the expectation for measurable integrands; never larger otherwise
--   - encoding: bins → integer labels read from integer cell $-1$; reason: an assignment is a labelling
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Theorem 1.4, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_OnlineBinCover_Supplement_Prophet

open Filter Topology

namespace OnlineBinCover.Supplement

/-- Theorem 1.4 (Single-sample prophet bin covering), p.5 (PDF p.6); proof Section 6 (Lemma 6.1,
Algorithm 1, pp.13–14) and Section E, pp.38–40.
Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

There is a randomized polynomial-time online algorithm `A_sp`: one program `P` of the real RAM
with coins (`RandProgram`), told `n` and one labelled sample `S_i` per distribution in advance and
then fed the online items with their labels (`spState`); on every coin tape, every sample and every
online sequence of sizes in `(0,1]`, every per-item run halts and the total work is at most
`C (n+1)^e`. There is one function `f` with `f(μ)/μ → 0` as `μ → ∞` such that for every `n`,
every collection of distributions `D_1, …, D_n` on `(0,1]` and every arrival order `τ` fixed
before the draws, `E[A_sp(X; S)] ≥ E[OPT(X)] − f(E[OPT(X)])`, with `S, X ∼ ∏ D_i` and the coin
tape independent, and only the online items counted. -/
theorem theorem_1_4 : ∃ P : PNormReg.Program, RandProgram P ∧ ∃ C e : ℕ,
    (∀ (n : ℕ) (S X : Fin n → ℝ), ValidSizes S → ValidSizes X →
      ∀ (τ : Equiv.Perm (Fin n)) (ω : ℕ → Bool),
        (∀ t < n, (spState P (C * (n + 1) ^ e) ω S X τ (t + 1)).halted = true) ∧
        (spState P (C * (n + 1) ^ e) ω S X τ n).work ≤ C * (n + 1) ^ e) ∧
    ∃ f : ℝ → ℝ, Tendsto (fun μ : ℝ => f μ / μ) atTop (𝓝 0) ∧
      ∀ (n : ℕ) (D : Fin n → MeasureTheory.ProbabilityMeasure ℝ),
        (∀ i, (D i : MeasureTheory.Measure ℝ) (Set.Ioc 0 1)ᶜ = 0) →
        ∀ τ : Equiv.Perm (Fin n),
          optExp D - f (optExp D) ≤ spExp P (C * (n + 1) ^ e) D τ := by sorry

end OnlineBinCover.Supplement
