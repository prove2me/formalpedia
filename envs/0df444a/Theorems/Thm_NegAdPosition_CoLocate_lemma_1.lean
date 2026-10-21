-- Prove2me | Theorems.Thm_NegAdPosition_CoLocate_lemma_1
-- name    : NegAdPosition.CoLocate.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:23.309533+00:00
-- url     : https://prove2.me/theorems/0d091ab6-031a-40fc-9f01-93c82d6843c6
-- title:
--   Lemma 1, p. 20 — apart, against a weak opponent negative advertising beats positive iff β > δ ≥ Π + σββ; otherwise positive wins
-- statement:
--   Suppose the entrant locates apart and consumers hold the Bayes beliefs of the strategies of the proof of Proposition 2. Let firm $i$ face a *weak* opponent, one that cannot advertise and therefore plays $\varnothing$. Write $D_i(a_i, a_{-i})$ for firm $i$'s demand. Under the standing assumptions and Assumption 1′, for each firm $i$:
--
--   1. negative advertising gives strictly more demand than positive advertising if and only if
--   $$\beta > \delta \ge \Pi + \sigma_\beta\beta,$$
--   that is, $D_i(P_i, \varnothing) < D_i(N_{-i}, \varnothing)$ exactly in this region;
--   2. outside this region positive advertising gives strictly more demand: $D_i(N_{-i}, \varnothing) < D_i(P_i, \varnothing)$.
--
--   The lemma shows when a firm located apart would attack a weak rival. In the equilibrium of Proposition 2 the region is excluded, so positive advertising is played against weak opponents apart.
--
--   **Formalization Note.** Assumption 1′ uses $\underline\gamma < -\Pi$ in place of the printed $\underline\gamma < \Pi$.
-- source:
--   Bostanci, Yildirim & Jerath, Negative Advertising and Competitive Product Positioning, authors' manuscript (Nov. 2021; Management Science 2023, doi:10.1287/mnsc.2022.4439), p. 20 (PDF 20), Lemma 1; proof p. A5 (PDF 48)

import Mathlib
import Definitions.Def_NegAdPosition_CoLocate_Model

namespace NegAdPosition.CoLocate

theorem lemma_1 (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (i : Firm) :
    (copnDemand P .R i .pos .none < copnDemand P .R i .neg .none ↔
        (P.δ < P.β ∧ P.Pi + P.σB * P.β ≤ P.δ)) ∧
      (¬ (P.δ < P.β ∧ P.Pi + P.σB * P.β ≤ P.δ) →
        copnDemand P .R i .neg .none < copnDemand P .R i .pos .none) := by sorry

end NegAdPosition.CoLocate
