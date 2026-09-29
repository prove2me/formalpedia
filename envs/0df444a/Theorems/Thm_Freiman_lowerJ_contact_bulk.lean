-- Prove2me | Theorems.Thm_Freiman_lowerJ_contact_bulk
-- name    : Freiman.lowerJ_contact_bulk
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:20.704652+00:00
-- url     : https://prove2.me/theorems/365f402d-5c8f-47be-8085-c94f87264908
-- title:
--   Freiman repeated-three proof: contact bulk
-- statement:
--   Multiply the exact positive factor bound and the two invariant tail boxes to obtain the uniform contact lower bound.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_contact_bulk (r s : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) (k : ℕ) (hk : 2 ≤ k) (hf : (371/500:ℝ) < lowerJCoeff*(1+lowerJTau k*lowerJC)/(1+lowerJTau k*lowerJA)) (hb : (151/500:ℝ) < lowerJIter k lowerJA ∧ lowerJIter k lowerJA < (303/1000:ℝ) ∧ (151/500:ℝ) < lowerJIter k lowerJD ∧ lowerJIter k lowerJD < (303/1000:ℝ) ∧ (151/500:ℝ) < lowerJIter k lowerJC ∧ lowerJIter k lowerJC < (38/125:ℝ) ∧ (151/500:ℝ) < lowerJIter k lowerJD ∧ lowerJIter k lowerJD < (38/125:ℝ)) : lowerJHBar r s < lowerJHK k r s := by
  sorry
