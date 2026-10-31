-- Prove2me | Theorems.Thm_NestedCRP_ncrp_exchangeable
-- name    : NestedCRP.ncrp_exchangeable
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:50.411686+00:00
-- url     : https://prove2.me/theorems/65b144de-4832-4629-9118-8aca5b049d30
-- title:
--   Exchangeability of the nested CRP
-- statement:
--   For $\gamma>0$, a permutation $\sigma$ of the tourists and a tree $T$,
--
--   $$
--   \mathrm{ncrp}(\sigma\cdot T)=\mathrm{ncrp}(T).
--   $$
--
--   The law on trees does not depend on the order in which the tourists arrive. This is what makes any document exchangeable with the last one, which the path sampler relies on.
--
--   Differences from the source:
--   - generalization: the CRP is invariant to the order of arrival of customers → the nested CRP on trees is invariant to the order of arrival of tourists; reason: the nCRP runs one CRP in each restaurant, and its first level is the single CRP of the source
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §3, p.7:10

import Mathlib
import Definitions.Def_NestedCRP_ncrpMass

namespace NestedCRP

/-- The nCRP is invariant under reordering the tourists. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §3, p.7:10 (stated for one
CRP; the nCRP needs it node by node). -/
theorem ncrp_exchangeable {D : ℕ} {γ : ℝ} (hγ : 0 < γ) (σ : Equiv.Perm (Fin D)) (T : Tree D) :
    ncrpMass γ (T.relabel σ) = ncrpMass γ T := by sorry

end NestedCRP
