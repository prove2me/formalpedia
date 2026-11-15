-- Prove2me | Theorems.Thm_LocalLLL_Main_Supplement_theorem_4_5
-- name    : LocalLLL.Main.Supplement.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T01:44:31.640197+00:00
-- url     : https://prove2.me/theorems/13b8c492-0968-49a7-acc7-bc8a12568f8d
-- title:
--   Theorem 4.5 — k-domatic partition for k ≤ δ/(2001 ln ∆)
-- statement:
--   Let $G$ be a graph with at most $n\ge1$ nodes, every degree at least $\delta$ and at most $\Delta$, and let $k\ge1$ be an integer with
--
--   $$k\le\frac{\delta}{2001\ln\Delta}.$$
--
--   There is a randomized LOCAL algorithm that, with probability at least $1-n^{-\gamma}$, computes a $k$-domatic partition of $G$, that is, a partition $V_1,\dots,V_k$ of the vertices such that every vertex $v$ and every $i$ satisfy $v\in V_i$ or $N(v)\cap V_i\neq\emptyset$, in at most $A\,(\log\log(n+16))^{B}$ rounds. The exponent $B$ is absolute and $A>0$ depends only on $\gamma>0$, not on $\delta$, $\Delta$, $k$ or $n$. The algorithm knows $n,\delta,\Delta,k$; nodes have no input besides their identifiers.
--
--   Since the domatic number is always at most $\delta+1$, the number of parts is within a factor $O(\log\Delta)$ of the trivial upper bound and within a constant factor of what is known to exist.
--
--   Differences from the source:
--   - generalization: δ and ∆ the minimum and maximum degree → δ any lower bound and ∆ any upper bound on all degrees; reason: the minimum and maximum degree are such bounds, so the statement specializes to the source
--   - encoding: k ≤ δ/(2001 ln ∆) → k ≤ δ/(2001 · ln ∆) as a real division; reason: for ∆ ≤ 1 the source's bound divides by ln ∆ = 0 and is undefined; Lean's x/0 = 0 then excludes every k ≥ 1, and no defined case is lost
--   - encoding: k the number of parts → a natural number k ≥ 1; reason: a partition into k parts presupposes k ≥ 1
--   - encoding: partition of V into k disjoint sets V_1, …, V_k → a map c : V → Fin k with V_i = c⁻¹(i); reason: same objects
--   - reading: poly(log log n) rounds with high probability → A · (log log(n + 16))^B rounds with one absolute B and A depending only on γ, failure at most n^(−γ) for every γ > 0; reason: Reading R of the published goal; w.h.p. is failure n^(−a) for any desired a (p. 2)
--   - encoding: n the number of nodes → n ≥ 1 an upper bound with card V ≤ n; nodes know n, δ, ∆, k; reason: the source allows n to be a global upper bound (p. 2) and the algorithm uses δ, ∆ and k
--   - encoding: success probability → outer measure of the failure set under the product fair-coin law at most n^(−γ); reason: published convention of the base mission
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), Theorem 4.5 and the definition of k-domatic partition before it, p. 12 (PDF 13); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Supplement_Corollaries

open MeasureTheory

noncomputable section

namespace LocalLLL.Main.Supplement

open LocalLLL.Main

/-- Theorem 4.5, printed p. 12 (PDF 13). `δ` bounds every degree from below and `Δ` from above;
`k ≥ 1` with `k ≤ δ/(2001 ln Δ)` (division form: `Δ ≤ 1` makes it unsatisfiable, as the
undefined `δ/0` is excluded). Exponent `B` absolute, `A` depending on `γ` only. -/
theorem theorem_4_5 :
    ∃ B : ℕ, ∀ γ : ℝ, 0 < γ → ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, 1 ≤ n → ∀ δ Δ k : ℕ, 1 ≤ k →
        (k : ℝ) ≤ (δ : ℝ) / (2001 * Real.log (Δ : ℝ)) →
        ∃ T : ℕ, (T : ℝ) ≤ A * loglog n ^ B ∧
        ∃ alg : LocalAlg Unit (Fin k),
          ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (id : V → ℕ),
            Function.Injective id → Fintype.card V ≤ n →
            (∀ v, δ ≤ degree G v) → (∀ v, degree G v ≤ Δ) →
            tapes V {ω | ¬ IsDomaticPartition G k (run alg T G id (fun _ => ()) ω)}
              ≤ ENNReal.ofReal ((n : ℝ) ^ (-γ)) := by sorry

end LocalLLL.Main.Supplement
