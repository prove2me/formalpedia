-- Prove2me | Theorems.Thm_NegAdPosition_CoLocate_table_1_colocation
-- name    : NegAdPosition.CoLocate.table_1_colocation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:17.521754+00:00
-- url     : https://prove2.me/theorems/d03506ed-b047-4d95-bc43-c44c5a32bf2c
-- title:
--   Table 1 (Co-location), p. 17 — posterior expected attributes after each advertising outcome when the entrant co-locates
-- statement:
--   Suppose the entrant co-locates ($x_2 = L$), so that the attributes of the two products are correlated with coefficient $\rho$, and both firms follow the advertising strategies of the proof of Proposition 2 with consumers forming Bayes posteriors. Under the standing assumptions (including $\sigma_\Pi\Pi = \sigma_\beta\beta$), for each firm $i$:
--
--   | $a_i$ | $a_{-i}$ | $E[A_i]$ | $E[A_{-i}]$ |
--   |---|---|---|---|
--   | $P_i$ | $P_{-i}$ | $(1-\sigma_\Pi)\Pi$ | $(1-\sigma_\Pi)\Pi$ |
--   | $P_i$ | $N_i$ | $(1-\sigma_\Pi)\Pi - (1-\sigma_\beta)\beta$ | $-\sigma_\Pi\Pi - \rho(1-\sigma_\beta)\beta$ |
--   | $N_{-i}$ | $N_i$ | $-\sigma_\Pi\Pi - (1-\sigma_\beta)\beta$ | $-\sigma_\Pi\Pi - (1-\sigma_\beta)\beta$ |
--   | $P_i$ | $\varnothing$ | $(1-\sigma_\Pi)\Pi + \sigma_\beta\beta$ | $-\sigma_\Pi\Pi + \rho\sigma_\beta\beta$ |
--   | $N_{-i}$ | $\varnothing$ | $-\sigma_\Pi\Pi + \sigma_\beta\beta$ | $-\sigma_\Pi\Pi - (1-\sigma_\beta)\beta$ |
--   | $\varnothing$ | $\varnothing$ | $-\sigma_\Pi\Pi + \sigma_\beta\beta$ | $-\sigma_\Pi\Pi + \sigma_\beta\beta$ |
--
--   The terms in $\rho$ are the paper's *spillover effect*: under co-location, learning that one product has (or lacks) the negative attribute shifts beliefs about the other.
--
--   These posteriors drive Lemmas 3 and 4 and the entrant's expected demand from co-locating.
--
--   **Formalization Note.** The entries are stated in the printed form, which uses $\sigma_\Pi\Pi = \sigma_\beta\beta$ from the standing assumptions. The posterior is the Bayes posterior of the strategies under the correlated prior.
-- source:
--   Bostanci, Yildirim & Jerath, Negative Advertising and Competitive Product Positioning, authors' manuscript (Nov. 2021; Management Science 2023, doi:10.1287/mnsc.2022.4439), p. 17 (PDF 17), Table 1, panel Co-location

import Mathlib
import Definitions.Def_NegAdPosition_CoLocate_Model

namespace NegAdPosition.CoLocate

theorem table_1_colocation (P : Params) (hS : P.Standing) (i : Firm) :
    copnPost P .L i .pos .pos i = (1 - P.σP) * P.Pi ∧
      copnPost P .L i .pos .pos i.other = (1 - P.σP) * P.Pi ∧
      copnPost P .L i .pos .neg i = (1 - P.σP) * P.Pi - (1 - P.σB) * P.β ∧
      copnPost P .L i .pos .neg i.other = -(P.σP * P.Pi) - P.ρ * (1 - P.σB) * P.β ∧
      copnPost P .L i .neg .neg i = -(P.σP * P.Pi) - (1 - P.σB) * P.β ∧
      copnPost P .L i .neg .neg i.other = -(P.σP * P.Pi) - (1 - P.σB) * P.β ∧
      copnPost P .L i .pos .none i = (1 - P.σP) * P.Pi + P.σB * P.β ∧
      copnPost P .L i .pos .none i.other = -(P.σP * P.Pi) + P.ρ * P.σB * P.β ∧
      copnPost P .L i .neg .none i = -(P.σP * P.Pi) + P.σB * P.β ∧
      copnPost P .L i .neg .none i.other = -(P.σP * P.Pi) - (1 - P.σB) * P.β ∧
      copnPost P .L i .none .none i = -(P.σP * P.Pi) + P.σB * P.β ∧
      copnPost P .L i .none .none i.other = -(P.σP * P.Pi) + P.σB * P.β := by sorry

end NegAdPosition.CoLocate
