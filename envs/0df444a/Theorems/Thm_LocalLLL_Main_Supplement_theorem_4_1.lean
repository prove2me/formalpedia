-- Prove2me | Theorems.Thm_LocalLLL_Main_Supplement_theorem_4_1
-- name    : LocalLLL.Main.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T01:43:19.873105+00:00
-- url     : https://prove2.me/theorems/85740abe-2db9-49a5-83c3-77cd000eb918
-- title:
--   Theorem 4.1 — failure-probability attenuation for locally checkable algorithms
-- statement:
--   Fix an upper bound $n\ge1$ on the number of nodes and an upper bound $\Delta\ge3$ on every degree. Let $\mathcal A$ be a randomized LOCAL algorithm run for $T$ rounds, and let $\mathcal C$ be a deterministic checker run for $R$ rounds that decides at each node whether that node's output of $\mathcal A$ is correct. Suppose every node is incorrect with probability at most $p$, where
--
--   $$p\,\Delta^{2000(T+R)}<1.$$
--
--   Then there is a LOCAL algorithm running in
--
--   $$(T+R)\cdot A\,\bigl(\log\log(n+16)\bigr)^{B}$$
--
--   rounds whose output is, with probability at least $1-n^{-\gamma}$, an output of $\mathcal A$ (the labelling $\mathcal A$ produces on some choice of tapes) at which every node is correct. The exponent $B$ is absolute; for each failure exponent $\gamma>0$ the constant $A>0$ depends on $\gamma$ only, not on $n,\Delta,T,R,p,\mathcal A,\mathcal C$ or the input and output types. The new algorithm may depend on $n,\Delta,T,R,p,\mathcal A,\mathcal C$, but is fixed before the graph, the identifiers and the inputs.
--
--   This is the error-attenuation result of Chang and Pettie combined with Theorem 1.1: a local algorithm whose node failures are rare relative to $\Delta^{-2000(T+R)}$ can be made to succeed everywhere with high probability, at a cost of a $\mathrm{poly}(\log\log n)$ factor that does not depend on $\Delta$.
--
--   Differences from the source:
--   - generalization: every node is incorrect with probability at most p (on every admissible graph) → the bound p is assumed only on the graph, identifiers and inputs on which the conclusion is asserted; reason: the conclusion for an instance needs the bound only on that instance; the source's uniform hypothesis implies the per-instance one
--   - generalization: ∆ the maximum degree → ∆ any upper bound on all degrees; reason: the maximum degree is one such bound, so the statement specializes to the source
--   - reading: each vertex can check in R(n, ∆) rounds if its output is correct → a deterministic R-round LOCAL checker that sees the identifiers and the (input, output) labels, run on the all-false tape; a node is correct when its verdict is true; reason: local checkability is decision by an R-round local algorithm; every deterministic one arises from a program that ignores its tape
--   - encoding: T(n, ∆), R(n, ∆) and p as functions of (n, ∆) → fixed values T, R, p for each fixed (n, ∆), with A and B uniform over them; reason: applying the fixed-(n, ∆) statement at every (n, ∆) gives the function form
--   - reading: (T + R) · poly(log log n) rounds, all nodes correct with high probability → (T + R) · A · (log log(n + 16))^B rounds with one absolute B and A depending only on γ, failure at most n^(−γ) for every γ > 0; reason: Reading R of the published goal; w.h.p. is failure n^(−a) for any desired a (p. 2)
--   - encoding: n the number of nodes → n ≥ 1 an upper bound with card V ≤ n, known to the algorithm; reason: the source allows n to be a global upper bound by padding (p. 2)
--   - encoding: success probability → outer measure of the failure set under the product fair-coin law at most n^(−γ), and the hypothesis likewise as an outer-measure bound; reason: published convention of the base mission; no measurability of arbitrary local computation is assumed
--   - encoding: produces an output of A → the output equals the run of A for T rounds on some tape assignment; reason: an output of A is a labelling A can produce
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), Theorem 4.1, p. 10 (PDF 11); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Supplement_Corollaries

open MeasureTheory

noncomputable section

namespace LocalLLL.Main.Supplement

open LocalLLL.Main

/-- Theorem 4.1, printed p. 10 (PDF 11). Exponent `B` absolute, `A` depending on `γ` only; for each
`(n, Δ)` the round bound is `(T + R) · A · (log log n)^B`, and the new algorithm is fixed before the
graph, the identifiers and the inputs. The per-node failure bound `p` is assumed on the instance
the new algorithm runs on. -/
theorem theorem_4_1 :
    ∃ B : ℕ, ∀ γ : ℝ, 0 < γ → ∃ A : ℝ, 0 < A ∧
      ∀ (I O : Type) (n : ℕ), 1 ≤ n → ∀ Δ : ℕ, 3 ≤ Δ → ∀ (T R : ℕ) (p : ℝ)
        (algA : LocalAlg I O) (chk : LocalAlg (I × O) Bool),
        p * (Δ : ℝ) ^ (2000 * (T + R)) < 1 →
        ∃ T' : ℕ, (T' : ℝ) ≤ ((T + R : ℕ) : ℝ) * A * loglog n ^ B ∧
        ∃ alg : LocalAlg I O,
          ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (id : V → ℕ) (input : V → I),
            Function.Injective id → Fintype.card V ≤ n → (∀ v, degree G v ≤ Δ) →
            (∀ v, tapes V {ω | checkAt chk R G id input (run algA T G id input ω) v = false}
                ≤ ENNReal.ofReal p) →
            tapes V {ω' | ¬ ((∃ ω, run alg T' G id input ω' = run algA T G id input ω) ∧
                allCorrect chk R G id input (run alg T' G id input ω'))}
              ≤ ENNReal.ofReal ((n : ℝ) ^ (-γ)) := by sorry

end LocalLLL.Main.Supplement
