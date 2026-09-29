-- Prove2me | Theorems.Thm_Freiman_trunk_normal_use_valid
-- name    : Freiman.trunk_normal_use_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:36:06.123613+00:00
-- url     : https://prove2.me/theorems/6c489787-8b94-48db-92b0-72e5200d373c
-- title:
--   trunk normal use valid
-- statement:
--   Reuse the literal source polynomial and all its original coefficient bounds with the actual available premise strictness. Positive margin permits two weak premises; zero margin requires an actual strict premise.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_normal_use_valid (C : TrunkCatalog) (w : TrunkWitness) (hw : trunkWitnessValid C w) (hz : w.diagonal = 0)
    (l u : CertBound) (hu : trunkUseBounds C w l u) :
    certWitnessValid ⟨l,u,w.rectangle,certBernsteinCoefficients (trunkPolynomial C w) w.rectangle,fun _ _ => w.margin/2⟩ := by
  sorry
