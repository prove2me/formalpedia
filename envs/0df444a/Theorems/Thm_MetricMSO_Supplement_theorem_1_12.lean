-- Prove2me | Theorems.Thm_MetricMSO_Supplement_theorem_1_12
-- name    : MetricMSO.Supplement.theorem_1_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:03:42.640748+00:00
-- url     : https://prove2.me/theorems/149d723e-8c15-4d9b-85ca-c21eff81b5d4
-- title:
--   Theorem 1.12 — dependence boundaries for EqDist and Close: bounded width and bounded component diameter
-- statement:
--   Let $\mathcal C$ be a graph class and let $R$ be $\mathrm{EqDist}$, $\mathrm{Close}$, or both predicates together. Write $D(G)$ for the maximum diameter of a connected component of $G$.
--
--   1. $\mathcal C$ is monadically $\mathrm{MSO}_2[R]$-dependent if and only if it has bounded treewidth and bounded component diameter; if $\mathcal C$ is hereditary, this is equivalent to bounded treedepth. The same holds for $\mathrm{CMSO}_2[R]$.
--   2. $\mathcal C$ is monadically $\mathrm{CMSO}_1[R]$-dependent if and only if it has bounded cliquewidth and bounded component diameter.
--
--   These logics have no $\mathrm{SP}$ or $\mathrm{EqGC}$ atom. Treedepth is the least height of a rooted forest on $V(G)$ in which every edge joins an ancestor and a descendant.
--
--   Differences from the source:
--   - encoding: an interpretation with symmetric irreflexive η → output adjacency a ≠ b ∧ η(a, b) ∧ η(b, a); reason: equal to η when η is symmetric and irreflexive, and definable in the same logic
--   - encoding: a graph class → a predicate on graphs SimpleGraph (Fin n), no closure assumption; reason: every finite graph is isomorphic to one on Fin n; dependence is invariant under isomorphism of the produced graphs
--   - encoding: R ∈ {EqDist, Close}, and both predicates → Boolean flags eq, cl with eq ∨ cl; reason: the three cases of the page
--   - encoding: an interpretation on the incidence structure I(G) with ν(x), η(x, y) over elements → a domain-formula pair (vertex, edge element) and four adjacency formulas, one per sort combination (IncInterp); reason: one formula over elements is equivalent to its case split by sort, in the same logic
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c5863…), Theorem 1.12, p.11 (PDF 13), restated p.46 (PDF 48); D(G) p.45 (PDF 47)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_MetricMSO_gcw
import Definitions.Def_SNPTreedepth_treedepth
import Definitions.Def_MetricMSO_Supplement_Interpretation

open PlantedSubgraphLD (tw)
open SNPTreedepth (treedepth)

namespace MetricMSO.Supplement

open MetricMSO

/-- **Theorem 1.12.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863),
p.11 (PDF 13), restated p.46 (PDF 48): "Let C be a graph class and let R ∈ {EqDist, Close}.
(i) The class C is monadically MSO2[R]-dependent if and only if it has bounded treewidth and bounded
component diameter. If C is hereditary, this is equivalent to bounded treedepth. (ii) The class C
is monadically CMSO1[R]-dependent if and only if it has bounded cliquewidth and bounded component
diameter. The characterization in (i) also holds for CMSO2[R], and all statements remain true when
both predicates are present."

For each choice of the unguarded predicates — `EqDist` alone (`eq = true, cl = false`), `Close`
alone (`eq = false, cl = true`), or both — and every graph class `C`:
1. for `MSO2[R]` and for `CMSO2[R]` on incidence structures: monadic dependence ⇔ bounded `tw` and
   bounded component diameter `D`; and if `C` is hereditary, monadic dependence ⇔ bounded
   treedepth;
2. for `CMSO1[R]` on adjacency structures: monadic dependence ⇔ bounded `cw` and bounded `D`.

**Formalization Note** These logics have no `SP` and no `EqGC` atom. Treedepth is the published
`SNPTreedepth.treedepth` (least height of a rooted forest whose closure contains `G`), treewidth the
published `PlantedSubgraphLD.tw`, cliquewidth the published `MetricMSO.cw`. -/
theorem theorem_1_12 (eq cl : Bool) (hR : (eq || cl) = true) (C : GraphClass) :
    (∀ card : Bool,
      (MonDepInc (Logic (incFeatures card false false eq cl)) C ↔
        BoundedOn (fun _ G => tw G) C ∧ BoundedOn (fun _ G => compDiam G) C) ∧
      (Hereditary C →
        (MonDepInc (Logic (incFeatures card false false eq cl)) C ↔
          BoundedOn (fun _ G => treedepth G) C))) ∧
    (MonDepAdj (Logic (adjFeatures true false false eq cl)) C ↔
      BoundedOn (fun _ G => cw G) C ∧ BoundedOn (fun _ G => compDiam G) C) := by sorry

end MetricMSO.Supplement
