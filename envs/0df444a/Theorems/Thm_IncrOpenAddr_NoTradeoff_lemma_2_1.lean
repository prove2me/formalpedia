-- Prove2me | Theorems.Thm_IncrOpenAddr_NoTradeoff_lemma_2_1
-- name    : IncrOpenAddr.NoTradeoff.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:35:37.834661+00:00
-- url     : https://prove2.me/theorems/798a4be5-5704-4114-8359-7fe3f7f2a8c4
-- title:
--   Lemma 2.1 — phase lengths: nonfinal phase j has between ⌊|T_{i−1}|/(10j²)⌋ and |T_{i−1}|/(5j²)+1 insertions; the final phase at least |T_{i−1}| − ⌊(1−η)|T_{i−1}|⌋
-- statement:
--   **Lemma 2.1 (Phase lengths).** In the schedule (1) with a sufficiently small constant $\eta>0$, for every table size $n\ge8$ and every epoch $i$ with $2\le i\le\alpha$, writing $T=|T_{i-1}|$ and $h$ for the height of $T_{i-1}$:
--
--   1. every nonfinal phase $j\in\{1,\dots,h\}$ of epoch $i$ consists of at least $\lfloor T/(10j^2)\rfloor$ and at most $T/(5j^2)+1$ insertions;
--   2. the final phase $h+1$ of epoch $i$ consists of at least $T-\lfloor(1-\eta)T\rfloor$ insertions.
--
--   $$\Big\lfloor\frac{|T_{i-1}|}{10j^2}\Big\rfloor\ \le\ \#\{\text{phase } j\}\ \le\ \frac{|T_{i-1}|}{5j^2}+1,\qquad \#\{\text{final phase}\}\ \ge\ |T_{i-1}|-\lfloor(1-\eta)|T_{i-1}|\rfloor.$$
--
--   Here $\#\{\text{phase }j\}$ (`phaseLength n η i j`) is the number of insertions $c+1$ with $t_{i-1}\le c<t_i$ whose phase is $j$. The second part is what lets the final phase alone finish cleaning up $T_{i-1}$ (Lemma 2.2); the first gives each nonfinal phase a $\Theta(1/j^2)$ share of the epoch.
--
--   Differences from the source:
--   - reading: η is a small constant, fixed by (6) η ≤ 1/(400(λ+1)^6) for a sufficiently large λ → ∃ η₀ > 0 such that the claim holds for every η ∈ (0, η₀]; reason: (6) with λ ≥ λ₀ is exactly η ≤ 1/(400(λ₀+1)^6); the claim is for the construction's fixed η, which may be any sufficiently small value
--   - reading: §2 assumes n a power of two; App. A.1 handles arbitrary n assuming n ≥ 8 'without loss of generality' → every n ≥ 8, with the App. A.1 layout (which for n a power of two is the §2 layout); reason: the paper's construction is only defined for n ≥ 8; smaller tables are a constant-size case of Theorem 1.1 only
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 9 (PDF 10), Lemma 2.1

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout

namespace IncrOpenAddr.NoTradeoff

theorem lemma_2_1 :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ n : ℕ, 8 ≤ n → ∀ i : ℕ, 2 ≤ i → i ≤ numTrees n →
        (∀ j : ℕ, 1 ≤ j → j ≤ height n (i - 1) →
          treeSize n (i - 1) / (10 * j ^ 2) ≤ phaseLength n η i j ∧
          (phaseLength n η i j : ℝ) ≤ (treeSize n (i - 1) : ℝ) / (5 * (j : ℝ) ^ 2) + 1) ∧
        treeSize n (i - 1) - ⌊(1 - η) * (treeSize n (i - 1) : ℝ)⌋₊ ≤
          phaseLength n η i (height n (i - 1) + 1) := by sorry

end IncrOpenAddr.NoTradeoff
