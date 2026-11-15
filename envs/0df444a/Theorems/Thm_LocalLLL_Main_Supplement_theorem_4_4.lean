-- Prove2me | Theorems.Thm_LocalLLL_Main_Supplement_theorem_4_4
-- name    : LocalLLL.Main.Supplement.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T01:44:09.801335+00:00
-- url     : https://prove2.me/theorems/77a41c64-9b35-4ea5-a346-051fc3b2bf67
-- title:
--   Theorem 4.4 — k-vertex splitting with discrepancy 80√((∆/k) ln ∆)
-- statement:
--   Let $G$ be a graph with at most $n\ge1$ nodes and every degree at most $\Delta$, and let $k$ be an integer with
--
--   $$2\le k\le \frac{\Delta}{6400\ln\Delta}.$$
--
--   There is a randomized LOCAL algorithm that, with probability at least $1-n^{-\gamma}$, computes a $k$-vertex splitting of discrepancy
--
--   $$80\sqrt{\frac{\Delta}{k}\,\ln\Delta},$$
--
--   that is, a partition $V_1,\dots,V_k$ of the vertices with $\bigl||N(v)\cap V_i|-\deg(v)/k\bigr|\le 80\sqrt{(\Delta/k)\ln\Delta}$ for every vertex $v$ and every $i$, in at most $A\,(\log\log(n+16))^{B}$ rounds. The exponent $B$ is absolute and $A>0$ depends only on $\gamma>0$, not on $\Delta$, $k$ or $n$. The algorithm knows $n,\Delta,k$; nodes have no input besides their identifiers.
--
--   For $k=2$ this splits every neighbourhood into two halves up to $O(\sqrt{\Delta\log\Delta})$ in $\mathrm{poly}(\log\log n)$ rounds, without the $\Delta$-dependent running time of earlier methods.
--
--   Differences from the source:
--   - generalization: ∆ the maximum degree → ∆ any upper bound on all degrees; reason: the maximum degree is one such bound, so the statement specializes to the source
--   - encoding: k ∈ [2, ∆/(6400 ln ∆)] → integer k with 2 ≤ k and k ≤ ∆/(6400 · ln ∆), division in ℝ; reason: for ∆ ≤ 1 the source's bound divides by ln ∆ = 0 and is undefined; Lean's x/0 = 0 then excludes every k ≥ 2, and no defined case is lost
--   - encoding: partition of V into k sets V_1, …, V_k → a map c : V → Fin k with V_i = c⁻¹(i), parts possibly empty; reason: when ∆ is the maximum degree an empty part is impossible, since at a vertex of degree ∆ it gives ∆/k ≤ 80√((∆/k) ln ∆), i.e. k ≥ ∆/(6400 ln ∆), and equality is excluded because ln ∆ is irrational for integers ∆ ≥ 2; so on the source's instances the two notions agree
--   - reading: poly(log log n) rounds w.h.p. → A · (log log(n + 16))^B rounds with one absolute B and A depending only on γ, failure at most n^(−γ) for every γ > 0; reason: Reading R of the published goal; w.h.p. is failure n^(−a) for any desired a (p. 2)
--   - encoding: n the number of nodes → n ≥ 1 an upper bound with card V ≤ n; nodes know n, ∆, k; reason: the source allows n to be a global upper bound (p. 2) and the algorithm uses ∆ and k
--   - encoding: success probability → outer measure of the failure set under the product fair-coin law at most n^(−γ); reason: published convention of the base mission
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), Theorem 4.4 and the definition of k-vertex splitting before it, p. 11 (PDF 12); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Supplement_Corollaries

open MeasureTheory

noncomputable section

namespace LocalLLL.Main.Supplement

open LocalLLL.Main

/-- Theorem 4.4, printed p. 11 (PDF 12). `Δ` bounds every degree; `k` is an integer in
`[2, Δ/(6400 ln Δ)]`. Exponent `B` absolute, `A` depending on `γ` only (not on `Δ`, `k`). Nodes
receive no input beyond their identifier; the algorithm knows `n`, `Δ`, `k`. -/
theorem theorem_4_4 :
    ∃ B : ℕ, ∀ γ : ℝ, 0 < γ → ∃ A : ℝ, 0 < A ∧
      ∀ n : ℕ, 1 ≤ n → ∀ Δ k : ℕ, 2 ≤ k →
        (k : ℝ) ≤ (Δ : ℝ) / (6400 * Real.log (Δ : ℝ)) →
        ∃ T : ℕ, (T : ℝ) ≤ A * loglog n ^ B ∧
        ∃ alg : LocalAlg Unit (Fin k),
          ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (id : V → ℕ),
            Function.Injective id → Fintype.card V ≤ n → (∀ v, degree G v ≤ Δ) →
            tapes V {ω | ¬ IsVertexSplitting G k
                (80 * Real.sqrt (((Δ : ℝ) / (k : ℝ)) * Real.log (Δ : ℝ)))
                (run alg T G id (fun _ => ()) ω)}
              ≤ ENNReal.ofReal ((n : ℝ) ^ (-γ)) := by sorry

end LocalLLL.Main.Supplement
