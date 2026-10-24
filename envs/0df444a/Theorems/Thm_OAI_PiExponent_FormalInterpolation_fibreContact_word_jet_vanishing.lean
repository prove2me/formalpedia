-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_word_jet_vanishing
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_word_jet_vanishing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:29:36.754427+00:00
-- url     : https://prove2.me/theorems/a5d3dc20-bf2f-416d-8b31-7bbf55988a54
-- title:
--   Derivative words preserve the reduced fibre jet threshold
-- statement:
--   If translated coefficients of a polynomial vanish strictly below weighted threshold `(1+3σ)N`, then coefficients of any successive partial derivative word vanish strictly below `(1+2σ)N`, provided the total derivative-word cost is at most `σN`. The strict inequality in the definition handles the equality boundary in the cost bound.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_word_jet_vanishing
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (V : Fin m → Rat) (sigma : Rat) (N : Nat)
    (F : MvPolynomial (Fin m) Complex)
    (hjet : fibreContactJetVanishing c V ((1 + 3 * (sigma : Real)) * (N : Real)) F)
    (word : List (Fin m))
    (hword : fibreContactWordCost V word ≤ (sigma : Real) * (N : Real)) :
    fibreContactJetVanishing c V ((1 + 2 * (sigma : Real)) * (N : Real))
      (fibreContactWord word F) := by sorry
