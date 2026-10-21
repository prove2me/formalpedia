-- Prove2me | Theorems.Thm_NegAdPosition_CoLocate_lemma_4
-- name    : NegAdPosition.CoLocate.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:25.476779+00:00
-- url     : https://prove2.me/theorems/5199a444-f641-4516-ad21-1c2fea668b43
-- title:
--   Lemma 4, p. 22 (boundary corrected) — co-located, against a strong opponent positive ads always win iff Π ≥ (1−ρ)(1−σβ)β
-- statement:
--   Suppose the entrant co-locates and consumers hold the Bayes beliefs of the strategies of the proof of Proposition 2. Let firm $i$ face a strong opponent, which plays $N_i$ or $P_{-i}$. Under the standing assumptions and Assumption 1′, for each firm $i$, positive advertising is strictly better against both actions of the opponent,
--   $$D_i(N_{-i}, N_i) < D_i(P_i, N_i) \quad\text{and}\quad D_i(N_{-i}, P_{-i}) < D_i(P_i, P_{-i}),$$
--   if and only if
--   $$\Pi \ge (1-\rho)(1-\sigma_\beta)\beta.$$
--   In particular condition (A1c), $\Pi > (1-\rho)(1-\sigma_\beta)\beta$, is sufficient.
--
--   The factor $1-\rho$ is the spillover effect: under co-location an attack on the rival's negative attribute also lowers beliefs about one's own product, which makes negative advertising less attractive.
--
--   **Formalization Note.** The paper states the condition with a strict inequality. At the boundary $\Pi = (1-\rho)(1-\sigma_\beta)\beta$ positive advertising against a negative attack produces an exact tie in expected utility, the buyers are split equally, and the positive advertisement still yields strictly more demand because it enlarges the market; so the paper's "only if" fails at that single boundary and the exact characterization is the weak inequality. The paper's sentence "Otherwise, negative advertising may be prioritized" has no definite content and is not formalized. Assumption 1′ uses $\underline\gamma < -\Pi$.
-- source:
--   Bostanci, Yildirim & Jerath, Negative Advertising and Competitive Product Positioning, authors' manuscript (Nov. 2021; Management Science 2023, doi:10.1287/mnsc.2022.4439), p. 22 (PDF 22), Lemma 4 (boundary corrected); proof p. A5 (PDF 48)

import Mathlib
import Definitions.Def_NegAdPosition_CoLocate_Model

namespace NegAdPosition.CoLocate

theorem lemma_4 (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (i : Firm) :
    (copnDemand P .L i .neg .neg < copnDemand P .L i .pos .neg ∧
        copnDemand P .L i .neg .pos < copnDemand P .L i .pos .pos) ↔
      (1 - P.ρ) * (1 - P.σB) * P.β ≤ P.Pi := by sorry

end NegAdPosition.CoLocate
