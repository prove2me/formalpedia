-- Prove2me | Theorems.Thm_NegAdPosition_CoLocate_table_1_apart
-- name    : NegAdPosition.CoLocate.table_1_apart
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:17.755869+00:00
-- url     : https://prove2.me/theorems/7263c8d2-d282-4901-989a-6c3a6b15a172
-- title:
--   Table 1 (Locating Apart), p. 17 — posterior expected attributes after each advertising outcome when the entrant locates apart
-- statement:
--   Suppose the entrant locates apart ($x_2 = R$) and both firms follow the advertising strategies of the proof of Proposition 2, with consumers forming Bayes posteriors. For a firm $i$ and an outcome in which $i$ plays $a_i$ and its rival plays $a_{-i}$, write $E[A_i]$ and $E[A_{-i}]$ for the consumers' posterior expected attributes. Under the standing assumptions (including $\sigma_\Pi\Pi = \sigma_\beta\beta$), for each firm $i$:
--
--   | $a_i$ | $a_{-i}$ | $E[A_i]$ | $E[A_{-i}]$ |
--   |---|---|---|---|
--   | $P_i$ | $P_{-i}$ | $(1-\sigma_\Pi)\Pi + \sigma_\beta\beta$ | $(1-\sigma_\Pi)\Pi + \sigma_\beta\beta$ |
--   | $P_i$ | $N_i$ | $(1-\sigma_\Pi)\Pi - (1-\sigma_\beta)\beta$ | $\sigma_\beta\beta$ |
--   | $N_{-i}$ | $N_i$ | $-(1-\sigma_\beta)\beta$ | $-(1-\sigma_\beta)\beta$ |
--   | $P_i$ | $\varnothing$ | $(1-\sigma_\Pi)\Pi + \sigma_\beta\beta$ | $-\sigma_\Pi\Pi$ |
--   | $N_{-i}$ | $\varnothing$ | $\sigma_\beta\beta - \sigma_\Pi\Pi$ | $-\sigma_\Pi\Pi - (1-\sigma_\beta)\beta$ |
--   | $\varnothing$ | $\varnothing$ | $-\sigma_\Pi\Pi + \sigma_\beta\beta$ | $-\sigma_\Pi\Pi + \sigma_\beta\beta$ |
--
--   Here $a_i = N_{-i}$ means firm $i$ advertises its rival's negative attribute and $a_{-i} = N_i$ means the rival advertises firm $i$'s negative attribute. The three remaining outcomes are the mirror images, obtained by exchanging the roles of the firms.
--
--   These posteriors are the inputs of every demand comparison in Lemmas 1 and 2 and of the entrant's expected demand from locating apart.
--
--   **Formalization Note.** The entries are stated in the printed form; some of them (for instance $(1-\sigma_\Pi)\Pi + \sigma_\beta\beta = \Pi$ in the first row) use the normalization $\sigma_\Pi\Pi = \sigma_\beta\beta$, which is part of the standing assumptions. The posterior is the Bayes posterior of the strategies over the 16 type profiles, not a table of numbers.
-- source:
--   Bostanci, Yildirim & Jerath, Negative Advertising and Competitive Product Positioning, authors' manuscript (Nov. 2021; Management Science 2023, doi:10.1287/mnsc.2022.4439), p. 17 (PDF 17), Table 1, panel Locating Apart

import Mathlib
import Definitions.Def_NegAdPosition_CoLocate_Model

namespace NegAdPosition.CoLocate

theorem table_1_apart (P : Params) (hS : P.Standing) (i : Firm) :
    copnPost P .R i .pos .pos i = (1 - P.σP) * P.Pi + P.σB * P.β ∧
      copnPost P .R i .pos .pos i.other = (1 - P.σP) * P.Pi + P.σB * P.β ∧
      copnPost P .R i .pos .neg i = (1 - P.σP) * P.Pi - (1 - P.σB) * P.β ∧
      copnPost P .R i .pos .neg i.other = P.σB * P.β ∧
      copnPost P .R i .neg .neg i = -((1 - P.σB) * P.β) ∧
      copnPost P .R i .neg .neg i.other = -((1 - P.σB) * P.β) ∧
      copnPost P .R i .pos .none i = (1 - P.σP) * P.Pi + P.σB * P.β ∧
      copnPost P .R i .pos .none i.other = -(P.σP * P.Pi) ∧
      copnPost P .R i .neg .none i = P.σB * P.β - P.σP * P.Pi ∧
      copnPost P .R i .neg .none i.other = -(P.σP * P.Pi) - (1 - P.σB) * P.β ∧
      copnPost P .R i .none .none i = -(P.σP * P.Pi) + P.σB * P.β ∧
      copnPost P .R i .none .none i.other = -(P.σP * P.Pi) + P.σB * P.β := by sorry

end NegAdPosition.CoLocate
