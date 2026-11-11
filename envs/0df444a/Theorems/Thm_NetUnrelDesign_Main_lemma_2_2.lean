-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_lemma_2_2
-- name    : NetUnrelDesign.Main.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:11:31.494064+00:00
-- url     : https://prove2.me/theorems/482e41b2-7ddf-4242-85b7-1d0bc6511d9f
-- title:
--   Lemma 2.2 — minimum cuts and components: Pr(K ≥ r) ≤ Pr(Bin(n, e^{−λ/2}) ≥ r) and e^{−λ} ≤ u ≤ Me^{−λ}
-- statement:
--   Let $G$ be the paper's connected multigraph on $n\ge2$ vertices, with nonnegative edge weights $w$. Edges fail independently with probability $e^{-w_e}$. Let $\lambda$ be the minimum cut weight, $K$ the number of working components, $u$ the disconnection probability and $M=\binom n2$. Let $Y\sim\mathrm{Bin}(n,e^{-\lambda/2})$. Then
--   $$\Pr(K\ge r)\le\Pr(Y\ge r)\qquad(2\le r\le n),\qquad e^{-\lambda}\le u\le Me^{-\lambda}.$$
--
--   Differences from the source:
--
--   - encoding: G is the paper's network (standing assumption of §1: connected, n ≥ 2) → hypotheses 2 ≤ n and IsConnectedGraph ends; reason: the paper's graph always satisfies them; no instance of the source is excluded
--   - encoding: Y ∼ Bin(n, e^{−λ/2}) and Pr(Y ≥ r) → binomTail n (e^{−λ/2}) r = Σ_{j=r}^{n} C(n,j) p^j (1−p)^{n−j}; reason: the binomial tail written out
--   - encoding: K, the number of components → Nat.card of the connected components of the working graph; reason: same quantity
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Lemma 2.2, p. 8 (PDF 9)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Prepared

open scoped BigOperators

namespace NetUnrelDesign.Main

/-- **Lemma 2.2 (Minimum cuts and components).** For the connected multigraph `G` (`n ≥ 2`) and
nonnegative edge weights `w` with minimum cut `λ`, let `Y ~ Bin(n, e^{−λ/2})`. Edges fail
independently with probability `e^{−w_e}`, and `K` is the number of working components. Then
`Pr(K ≥ r) ≤ Pr(Y ≥ r)` for `2 ≤ r ≤ n`, and `e^{−λ} ≤ u ≤ M e^{−λ}` with `M = n(n−1)/2`.
Sun 2026, p. 8 (PDF 9). -/
theorem lemma_2_2 {n m : ℕ} (ends : Ends n m) (hn : 2 ≤ n) (hconn : IsConnectedGraph ends)
    (w : Fin m → ℝ) (hw : ∀ e, 0 ≤ w e) :
    (∀ r : ℕ, 2 ≤ r → r ≤ n →
      prob (expNeg w) (fun F => r ≤ numComponents ends F) ≤
        binomTail n (Real.exp (-minCut ends w / 2)) r) ∧
    Real.exp (-minCut ends w) ≤ unrelW ends w ∧
    unrelW ends w ≤ pairCount n * Real.exp (-minCut ends w) := by sorry

end NetUnrelDesign.Main
