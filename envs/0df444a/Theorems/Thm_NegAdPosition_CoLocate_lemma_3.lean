-- Prove2me | Theorems.Thm_NegAdPosition_CoLocate_lemma_3
-- name    : NegAdPosition.CoLocate.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:22.344401+00:00
-- url     : https://prove2.me/theorems/b824b6c8-85c5-4c76-b4fd-d0734eb471c2
-- title:
--   Lemma 3, p. 21 — co-located, against a weak opponent positive advertising strictly beats negative advertising
-- statement:
--   Suppose the entrant co-locates with the incumbent and consumers hold the Bayes beliefs of the strategies of the proof of Proposition 2. Let firm $i$ face a weak opponent, which plays $\varnothing$. Under the standing assumptions and Assumption 1′, for each firm $i$,
--   $$D_i(N_{-i}, \varnothing) < D_i(P_i, \varnothing),$$
--   so positive advertising is always prioritized over negative advertising.
--
--   Under co-location any advertising advantage steals the rival's consumers, so the market-expanding positive advertisement wins.
--
--   **Formalization Note.** Assumption 1′ uses $\underline\gamma < -\Pi$.
-- source:
--   Bostanci, Yildirim & Jerath, Negative Advertising and Competitive Product Positioning, authors' manuscript (Nov. 2021; Management Science 2023, doi:10.1287/mnsc.2022.4439), p. 21 (PDF 21), Lemma 3

import Mathlib
import Definitions.Def_NegAdPosition_CoLocate_Model

namespace NegAdPosition.CoLocate

theorem lemma_3 (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (i : Firm) :
    copnDemand P .L i .neg .none < copnDemand P .L i .pos .none := by sorry

end NegAdPosition.CoLocate
