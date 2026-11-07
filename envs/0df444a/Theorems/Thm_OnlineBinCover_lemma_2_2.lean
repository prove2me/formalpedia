-- Prove2me | Theorems.Thm_OnlineBinCover_lemma_2_2
-- name    : OnlineBinCover.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:21.782006+00:00
-- url     : https://prove2.me/theorems/4feab7f3-7e2f-491f-8aa4-9dd8765363dd
-- title:
--   Lemma 2.2 — computing a basic LP solution with $\sum_C\lfloor x_C\rfloor\ge(1-4\varepsilon)\mathrm{OPT}(I)-(K+5)$
-- statement:
--   Let $0<\varepsilon<1/8$ and $K=\lceil\varepsilon^{-2}\rceil$. There is one deterministic program of the real RAM and constants $C,k$ such that, for every instance $I$ of $n$ items with sizes in $(0,1]$, the program run on $(n,\varepsilon,s_1,\dots,s_n)$ halts within
--
--   $$C\,(n+\lceil1/\varepsilon\rceil+1)^k$$
--
--   steps and outputs a basic feasible solution $x$ of the configuration LP (3) of $I$ (classification, linear grouping and configurations as in §2.1) with at most $K+1$ positive variables such that $y_C=\lfloor x_C\rfloor$ satisfies
--
--   $$\sum_{C}y_C\ge(1-4\varepsilon)\,\mathrm{OPT}(I)-(K+5).$$
--
--   The lemma is cited from Jansen and Solis-Oba [JSO03]; the blueprint of every algorithm in the paper is built from its output.
--
--   Differences from the source:
--   - reading: "we can compute … in time polynomial in the input size and $1/\varepsilon$" → one deterministic program of `PNormReg.Machine` halting within $C(n+\lceil1/\varepsilon\rceil+1)^k$ steps, input and output in the layout `lpInput`/`decodeLP`; reason: the paper names no machine; sizes are real numbers, so the exact real RAM
--   - encoding: basic feasible solution → the columns of the positive variables and the unit columns of the positive slacks are linearly independent; reason: the standard notion for the LP in equality form
--   - encoding: a configuration is a multiset of rounded large items → a count vector using only nonempty groups with rounded volume $<2$; reason: a multiset is its count vector; an empty group has no rounded item
--   - encoding: ties resolved consistently across $I$ and its subsets → ties broken by the item label; reason: a consistent rule, as p.6 requires
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Lemma 2.2, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_OnlineBinCover_LPOutput
import Definitions.Def_OnlineBinCover_Online

namespace OnlineBinCover

/-- Lemma 2.2 (LP approximation [JSO03]), p.8. Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…).

There is one deterministic program of the real RAM `PNormReg.Machine` which, on input
`n, ε, s₁, …, sₙ` (layout `lpInput`) with sizes in `(0, 1]` and `0 < ε < 1/8`, halts within
`C · (n + ⌈1/ε⌉ + 1)^k` steps (polynomial in the input size and `1/ε`) and outputs (layout
`decodeLP`) a basic feasible solution `x` of LP (3) for the instance, with at most `K + 1` positive
variables, such that `∑_C ⌊x_C⌋ ≥ (1 − 4ε) OPT(I) − (K + 5)` (`LPSpec s univ ε x`). -/
theorem lemma_2_2 : ∃ P : PNormReg.Program, DetANN.DetProgram P ∧ ∃ C k : ℕ,
    ∀ (n : ℕ) (s : Fin n → ℝ), ValidSizes s → ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      (PNormReg.run P (lpInput s ε) DetANN.detTape (C * (n + ⌈1 / ε⌉₊ + 1) ^ k)).halted = true ∧
      (PNormReg.run P (lpInput s ε) DetANN.detTape (C * (n + ⌈1 / ε⌉₊ + 1) ^ k)).work ≤
        C * (n + ⌈1 / ε⌉₊ + 1) ^ k ∧
      LPSpec s Finset.univ ε
        (decodeLP ε (PNormReg.run P (lpInput s ε) DetANN.detTape (C * (n + ⌈1 / ε⌉₊ + 1) ^ k))) := by sorry

end OnlineBinCover
