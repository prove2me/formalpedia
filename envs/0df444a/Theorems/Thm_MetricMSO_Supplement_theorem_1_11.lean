-- Prove2me | Theorems.Thm_MetricMSO_Supplement_theorem_1_11
-- name    : MetricMSO.Supplement.theorem_1_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:03:08.803514+00:00
-- url     : https://prove2.me/theorems/b7d7de40-7280-4110-b274-07f7ec3d984e
-- title:
--   Theorem 1.11 — bounded ctw and bounded gcw are exactly monadic dependence for the guarded logics
-- statement:
--   For every graph class $\mathcal C$, without closure assumptions:
--
--   1. $\mathcal C$ has bounded bag-connected treewidth $\mathrm{ctw}$ if and only if it is monadically $\mathrm{MSO}_2[\mathrm{EqGC}]$-dependent, if and only if it is monadically $\mathrm{MSO}_2[\mathrm{SP},\mathrm{EqGC}]$-dependent, and the same holds for the counting extensions $\mathrm{CMSO}_2[\mathrm{EqGC}]$ and $\mathrm{CMSO}_2[\mathrm{SP},\mathrm{EqGC}]$ (incidence structures, vertex and edge colors);
--   2. $\mathcal C$ has bounded geodesic cliquewidth $\mathrm{gcw}=\mathrm{cw}+\mathrm{cbl}$ if and only if it is monadically $\mathrm{CMSO}_1[\mathrm{EqGC}]$-dependent, if and only if it is monadically $\mathrm{CMSO}_1[\mathrm{SP},\mathrm{EqGC}]$-dependent (adjacency structures, vertex colors).
--
--   Here a class is monadically $L$-dependent when no fixed $L$-interpretation produces every finite graph from monadic lifts of its members, metric atoms being evaluated in the input graph.
--
--   Differences from the source:
--   - encoding: an interpretation with symmetric irreflexive η → output adjacency a ≠ b ∧ η(a, b) ∧ η(b, a); reason: equal to η when η is symmetric and irreflexive, and definable in the same logic
--   - encoding: a graph class → a predicate on graphs SimpleGraph (Fin n), no closure assumption; reason: every finite graph is isomorphic to one on Fin n; dependence is invariant under isomorphism of the produced graphs
--   - encoding: an interpretation on the incidence structure I(G) with ν(x), η(x, y) over elements → a domain-formula pair (vertex, edge element) and four adjacency formulas, one per sort combination (IncInterp); reason: one formula over elements is equivalent to its case split by sort, in the same logic
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c5863…), Theorem 1.11, p.10 (PDF 12), restated p.46 (PDF 48)

import Mathlib
import Definitions.Def_MetricMSO_ctw
import Definitions.Def_MetricMSO_gcw
import Definitions.Def_MetricMSO_Supplement_Interpretation

namespace MetricMSO.Supplement

open MetricMSO

/-- **Theorem 1.11.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863),
p.10 (PDF 12), restated p.46 (PDF 48): "For every graph class C, the following statements hold.
(i) The class C has bounded bag-connected treewidth if and only if it is monadically
MSO2[EqGC]-dependent, and equivalently if and only if it is monadically MSO2[SP, EqGC]-dependent.
(ii) The class C has bounded geodesic cliquewidth if and only if it is monadically
CMSO1[EqGC]-dependent, and equivalently if and only if it is monadically CMSO1[SP, EqGC]-dependent.
The equivalences in (i) also hold for the counting extensions of both logics."

For every graph class `C` (no closure assumption):
1. bounded `ctw` ⇔ monadically MSO2[EqGC]-dependent ⇔ monadically MSO2[SP, EqGC]-dependent ⇔
   monadically CMSO2[EqGC]-dependent ⇔ monadically CMSO2[SP, EqGC]-dependent, on incidence
   structures (vertex and edge colors, vertex and edge elements as output vertices);
2. bounded `gcw` ⇔ monadically CMSO1[EqGC]-dependent ⇔ monadically CMSO1[SP, EqGC]-dependent, on
   adjacency structures (vertex colors).

**Formalization Note** `incFeatures card sp eqgc eq cl` and `adjFeatures …` select the logic: the
counting atoms (`card`), `SP`, `EqGC`, and no unguarded metric atom. -/
theorem theorem_1_11 (C : GraphClass) :
    ((BoundedOn (fun _ G => ctw G) C ↔
        MonDepInc (Logic (incFeatures false false true false false)) C) ∧
      (BoundedOn (fun _ G => ctw G) C ↔
        MonDepInc (Logic (incFeatures false true true false false)) C) ∧
      (BoundedOn (fun _ G => ctw G) C ↔
        MonDepInc (Logic (incFeatures true false true false false)) C) ∧
      (BoundedOn (fun _ G => ctw G) C ↔
        MonDepInc (Logic (incFeatures true true true false false)) C)) ∧
    ((BoundedOn (fun _ G => gcw G) C ↔
        MonDepAdj (Logic (adjFeatures true false true false false)) C) ∧
      (BoundedOn (fun _ G => gcw G) C ↔
        MonDepAdj (Logic (adjFeatures true true true false false)) C)) := by sorry

end MetricMSO.Supplement
