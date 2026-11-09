-- Prove2me | Theorems.Thm_HypRecov_lemma_D_3
-- name    : HypRecov.lemma_D_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:37:39.645216+00:00
-- url     : https://prove2.me/theorems/39e4b70d-2009-4047-9fd6-0eaee41918ad
-- title:
--   Lemma D.3 — endpoint characterization of a bridge cut
-- statement:
--   Let $H$ be a simple $r$-uniform hypergraph on $V$ with $r\ge2$ and $G=G(H)$ its pair-support graph. For every $S\subseteq V$,
--   $$U_G(S)=\bigcup_{e\in\delta_H(S)}e .$$
--   Consequently $b_G(S)>0$ implies $b_G(S)\ge r$, and $b_G(S)=r$ if and only if $\mathrm{cut}_H(S)=1$.
--
--   A bridge cut of $H$ is thus recognized, and its edge read off, from the pair-support graph alone.
--
--   Differences from the source:
--   - encoding: G the simple pair-support graph of H → the two-section of E; reason: same graph (§2, p.5)
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma D.3, p.37 (PDF p.38)

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_twoSection
import Definitions.Def_HypRecov_incident

namespace HypRecov

/-- **Lemma D.3 (Endpoint characterization of a bridge cut).** Zhang, Chen, Shen, *Hypergraph Recovery
from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Lemma D.3,
p.37 (PDF p.38): "For every S ⊆ V, U_G(S) = ⋃_{e∈δ_H(S)} e. Consequently, b_G(S) > 0 implies
b_G(S) ≥ r, and b_G(S) = r if and only if cut_H(S) = 1." Here `G` is "the simple pair-support graph
of H" (p.37), i.e. its two-section, and `H` is simple and `r`-uniform with `r ≥ 2` (Theorem D.1). -/
theorem lemma_D_3 {n : ℕ} (E : Finset (Finset (Fin n))) (r : ℕ) (hr : 2 ≤ r)
    (hE : ∀ e ∈ E, e.card = r) (S : Finset (Fin n)) :
    incident (twoSection E) S = (bdry E S).biUnion id ∧
    (0 < (incident (twoSection E) S).card → r ≤ (incident (twoSection E) S).card) ∧
    ((incident (twoSection E) S).card = r ↔ cut E S = 1) := by sorry

end HypRecov
