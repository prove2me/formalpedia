-- Prove2me | Theorems.Thm_LocalLemmaHierarchy_Completeness_proposition_3_10
-- name    : LocalLemmaHierarchy.Completeness.proposition_3_10
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T00:21:19.400882+00:00
-- url     : https://prove2.me/theorems/6d820acd-f226-4170-9c53-f2f7f047fc8a
-- title:
--   Proposition 3.10 — the order of the rate: on $C_n$, $R=1/(4\cos^2(\pi/2n))$ and $R_q=1/4$
-- statement:
--   For independent sets on the cycle $C_n$, $n\ge4$, with any local orders,
--   $R=1/(4\cos^2(\pi/(2n)))$ and $R_q=1/4$ for $1\le q\le n-3$. At $q=n-3$,
--   $$R_q=R\cos^2\frac{\pi}{2(q+3)},\qquad R-R_q=\frac14\tan^2\frac{\pi}{2(q+3)}\ge\frac{\pi^2}{16(q+3)^2}.\qquad(3.11)$$
--   Matchings on $C_n$ have the same $R$ and $R_q=1/4$ for $1\le q\le n-2$.
--
--   Differences from the source:
--   - encoding: C_n with any local orders; R, R_q of the independent-set and matching families → SimpleGraph.cycleGraph n on Fin n, any NeighborOrders; uniformRadius (indepPoly C_n) / (matchPoly C_n) and memRadius (indRep C_n o) / (matchRep C_n); reason: the families and representations of App. E.1–E.2
--   - encoding: the identities (3.11) between the real numbers R, R_q at q = n − 3 → stated for toReal of the ℝ≥0∞ values, with q + 3 written ((n − 3 : ℕ) : ℝ) + 3; reason: R and R_q are finite by the first two conjuncts; n ≥ 4 makes n − 3 exact
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Proposition 3.10, printed p. 10 (PDF p. 12); proof App. B.7, printed p. 20 (PDF p. 22)

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Definitions.Def_LocalLemmaHierarchy_Completeness_Histories
import Definitions.Def_LocalLemmaHierarchy_Completeness_Memory
import Definitions.Def_LocalLemmaHierarchy_Completeness_Graph

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

/-- **Proposition 3.10 (The order of the rate)**, printed p. 10 / PDF 12 (proof App. B.7, printed 20
/ PDF 22). For independent sets on `C_n`, `n ≥ 4`, with any local orders,
`R = 1/(4 cos²(π/(2n)))` and `R_q = 1/4` for `1 ≤ q ≤ n − 3`; at `q = n − 3`,
`R_q = R cos²(π/(2(q+3)))` and `R − R_q = ¼ tan²(π/(2(q+3))) ≥ π²/(16(q+3)²)` (3.11). Matchings on
`C_n` have the same `R` and `R_q = 1/4` for `1 ≤ q ≤ n − 2`. -/
theorem proposition_3_10 (n : ℕ) (hn : 4 ≤ n) (o : NeighborOrders (SimpleGraph.cycleGraph n)) :
    uniformRadius (indepPoly (SimpleGraph.cycleGraph n)) =
        ENNReal.ofReal (1 / (4 * Real.cos (Real.pi / (2 * n)) ^ 2)) ∧
    (∀ q : ℕ, 1 ≤ q → q ≤ n - 3 →
      memRadius (indRep (SimpleGraph.cycleGraph n) o) q = ENNReal.ofReal (1 / 4)) ∧
    ((memRadius (indRep (SimpleGraph.cycleGraph n) o) (n - 3)).toReal =
        (uniformRadius (indepPoly (SimpleGraph.cycleGraph n))).toReal *
          Real.cos (Real.pi / (2 * (((n - 3 : ℕ) : ℝ) + 3))) ^ 2 ∧
      (uniformRadius (indepPoly (SimpleGraph.cycleGraph n))).toReal -
          (memRadius (indRep (SimpleGraph.cycleGraph n) o) (n - 3)).toReal =
        1 / 4 * Real.tan (Real.pi / (2 * (((n - 3 : ℕ) : ℝ) + 3))) ^ 2 ∧
      Real.pi ^ 2 / (16 * (((n - 3 : ℕ) : ℝ) + 3) ^ 2) ≤
        1 / 4 * Real.tan (Real.pi / (2 * (((n - 3 : ℕ) : ℝ) + 3))) ^ 2) ∧
    uniformRadius (matchPoly (SimpleGraph.cycleGraph n)) =
        ENNReal.ofReal (1 / (4 * Real.cos (Real.pi / (2 * n)) ^ 2)) ∧
    ∀ q : ℕ, 1 ≤ q → q ≤ n - 2 →
      memRadius (matchRep (SimpleGraph.cycleGraph n)) q = ENNReal.ofReal (1 / 4) := by sorry

end LocalLemmaHierarchy.Completeness
