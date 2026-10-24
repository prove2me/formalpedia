-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_fullRowRank_coefficients
-- name    : OAI.PiExponent.DeterminantContradiction.fullRowRank_coefficients
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:19:10.309777+00:00
-- url     : https://prove2.me/theorems/9c2304fc-f3c2-47e1-b580-62f7f1c82fb7
-- title:
--   Independent matrix rows realize arbitrary row values
-- statement:
--   For a matrix with finitely many rows and columns, linear independence of its row vectors implies that every assignment of values to the rows is obtained by a linear combination of the columns.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

theorem OAI.PiExponent.DeterminantContradiction.fullRowRank_coefficients
    {α β : Type} [Fintype α] [Fintype β]
    (M : Matrix α β ℂ)
    (hrows : LinearIndependent ℂ (fun a : α => M a)) :
    ∀ y : α → ℂ, ∃ c : β → ℂ, ∀ a : α,
      ∑ b : β, c b * M a b = y a := by sorry
