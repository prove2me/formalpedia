-- Prove2me | Theorems.Thm_NegAdPosition_CoLocate_lemma_2
-- name    : NegAdPosition.CoLocate.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:28.472055+00:00
-- url     : https://prove2.me/theorems/a37f871a-7f95-426f-b7e7-67aeab71f11c
-- title:
--   Lemma 2, p. 21 — apart, against a strong opponent negative advertising is prioritized iff (A1a) and (A1b)
-- statement:
--   Suppose the entrant locates apart and consumers hold the Bayes beliefs of the strategies of the proof of Proposition 2. Let firm $i$ face a *strong* opponent, which plays negative advertising $N_i$ or positive advertising $P_{-i}$. Write $D_i(a_i, a_{-i})$ for firm $i$'s demand. Under the standing assumptions and Assumption 1′, for each firm $i$, negative advertising is the better reply to both actions of the opponent, namely
--   $$D_i(P_i, N_i) < D_i(N_{-i}, N_i) \quad\text{and}\quad D_i(P_i, P_{-i}) \le D_i(N_{-i}, P_{-i}),$$
--   if and only if
--   $$\text{(i)}\ \ \beta > (1-\sigma_\Pi)\Pi + \delta \qquad\text{and}\qquad \text{(ii)}\ \ \bar\gamma + \sigma_\beta\beta \ge (1-\sigma_\Pi)\Pi + \delta.$$
--
--   This is the "negative advertising war" of the off-equilibrium path: when firms locate apart and both can attack, they do.
--
--   **Formalization Note.** The paper's "Otherwise, it prioritizes positive advertising" is the negation of the left-hand side and needs no separate clause. Assumption 1′ uses $\underline\gamma < -\Pi$.
-- source:
--   Bostanci, Yildirim & Jerath, Negative Advertising and Competitive Product Positioning, authors' manuscript (Nov. 2021; Management Science 2023, doi:10.1287/mnsc.2022.4439), p. 21 (PDF 21), Lemma 2; proof p. A5 (PDF 48), (A2), (A3)

import Mathlib
import Definitions.Def_NegAdPosition_CoLocate_Model

namespace NegAdPosition.CoLocate

theorem lemma_2 (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (i : Firm) :
    (copnDemand P .R i .pos .neg < copnDemand P .R i .neg .neg ∧
        copnDemand P .R i .pos .pos ≤ copnDemand P .R i .neg .pos) ↔
      (P.A1a ∧ P.A1b) := by sorry

end NegAdPosition.CoLocate
