-- Prove2me | Theorems.Thm_MetricMSO_lemma_2_1
-- name    : MetricMSO.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:55.821174+00:00
-- url     : https://prove2.me/theorems/2cb393ce-bdfe-4c41-9a1f-f8ad26ef365b
-- title:
--   Lemma 2.1 — the longest cycle of a minimum cycle basis is $\mathrm{cbl}(G)$
-- statement:
--   Let $G$ be a finite graph and let $\mathcal B_{\min}$ be a minimum cycle basis of $G$, that is, a cycle basis minimizing the sum of the lengths of its cycles. Then
--   $$\max_{C\in\mathcal B_{\min}}|E(C)|=\mathrm{cbl}(G),$$
--   where the maximum over the empty basis of a forest is $0$.
--
--   The statement identifies the parameter $\mathrm{cbl}$ with a quantity that Horton's algorithm computes.
--
--   Differences from the source:
--   - encoding: L = 0 when G is a forest, otherwise L := max over B_min of |E(C)| → Finset.univ.sup of the cycle lengths of B_min; reason: the supremum over the empty family is 0, so the two cases are one formula
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), Lemma 2.1, p.13 (PDF 15)

import Mathlib
import Definitions.Def_MetricMSO_cbl

namespace MetricMSO

/-- **Lemma 2.1** ([CGH95, Theorem 4]). Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.13 (PDF 15):
"Let Bmin be a minimum cycle basis of G. Set L = 0 when G is a forest, and otherwise set
L := maxC∈Bmin |E(C)|. Then L = cbl(G)."

**Formalization Note** The largest cycle length of the family, `Finset.univ.sup`, is `0` on the empty
family, which is the basis of a forest; so the page's two cases are one formula. -/
theorem lemma_2_1 {V : Type} [Fintype V] (G : SimpleGraph V) {k : ℕ} (B : Fin k → CycleOf G)
    (hB : IsMinCycleBasis B) :
    Finset.univ.sup (fun i => (B i).walk.length) = cbl G := by sorry

end MetricMSO
