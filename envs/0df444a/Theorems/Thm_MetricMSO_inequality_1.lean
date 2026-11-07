-- Prove2me | Theorems.Thm_MetricMSO_inequality_1
-- name    : MetricMSO.inequality_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:24.214292+00:00
-- url     : https://prove2.me/theorems/9eb2cb97-7dba-4051-bd88-fb996e83b217
-- title:
--   Inequality (1) — $\mathrm{cbl}(G)\le\mathrm{gcl}(G)\le2\,\mathrm{ctw}(G)$, with $\mathrm{tw}(G)\le\mathrm{ctw}(G)$
-- statement:
--   For every finite graph $G$,
--   $$\mathrm{cbl}(G)\le\mathrm{gcl}(G)\le2\,\mathrm{ctw}(G),$$
--   and $\mathrm{tw}(G)\le\mathrm{ctw}(G)$.
--
--   These bounds convert the parameter $|\varphi|+\mathrm{tw}(G)+\mathrm{cbl}(G)$ into $|\varphi|+\mathrm{ctw}(G)$ in the proof of the goal. The two inequalities of (1) are cited from Georgakopoulos–Sprüssel and Diestel–Müller.
--
--   Differences from the source:
--   - encoding: inequality (1) and the sentence "we have tw(G) ≤ ctw(G)" on the page before → one conjunction of the three inequalities; reason: both are stated in §2.3; nothing is added
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), inequality (1), p.14 (PDF 16); §2.3, p.13 (PDF 15), for tw(G) ≤ ctw(G)

import Mathlib
import Definitions.Def_MetricMSO_cbl
import Definitions.Def_MetricMSO_gcl
import Definitions.Def_MetricMSO_ctw
import Definitions.Def_PlantedSubgraphLD_tw

open PlantedSubgraphLD (tw)

namespace MetricMSO

/-- **Inequality (1), with `tw ≤ ctw`.** Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), p.14 (PDF 16):
"cbl(G) ≤ gcl(G) ≤ 2 ctw(G). (1)"; p.13 (PDF 15): "Since a bag-connected tree decomposition is also a
tree decomposition, we have tw(G) ≤ ctw(G)."

**Formalization Note** All parameters are natural numbers, with the graph on no vertex at `0`. -/
theorem inequality_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    cbl G ≤ gcl G ∧ gcl G ≤ 2 * ctw G ∧ tw G ≤ ctw G := by sorry

end MetricMSO
