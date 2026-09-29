-- Prove2me | Theorems.Thm_GeneralCK_Certificates_BivariateProvedProgram_value_pos_of_accepted_taylor
-- name    : GeneralCK.Certificates.BivariateProvedProgram.value_pos_of_accepted_taylor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T23:01:31.356931+00:00
-- url     : https://prove2.me/theorems/143f2193-bf73-44bf-b81e-18adcc6f19bf
-- title:
--   Positive values from accepted center and whole-cell Taylor certificates
-- statement:
--   Suppose center and whole-cell instruction lists have matching shapes and both satisfy the accepted-program obligations. Assume their initial intervals contain the corresponding real jets, the jets are directionally consistent on $[0,1]$, and nonnegative radii bound the two displacements. A strictly positive Taylor lower bound computed from the final center and whole-cell boxes implies a strictly positive real value in the chosen output register at the segment endpoint.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/BivariateProvedProgram.lean#L144-L164

import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.BivariateProvedProgram
open BivariateJetProgram Set

theorem GeneralCK.Certificates.BivariateProvedProgram.value_pos_of_accepted_taylor {p q : ℕ}
    (center : List (_root_.GeneralCK.Certificates.BivariateProvedProgram.Instruction p)) (whole : List (_root_.GeneralCK.Certificates.BivariateProvedProgram.Instruction q))
    {centerInputs : List (DyadicBivariateJetEnclosure p)}
    {wholeInputs : List (DyadicBivariateJetEnclosure q)} {jets : List BivariateJet2}
    (i : ℕ) {da dz ra rz : ℝ}
    (hshape : shapes center=shapes whole)
    (hc : RegistersContain centerInputs jets 0)
    (hw : ∀ t ∈ Icc (0:ℝ) 1, RegistersContain wholeInputs jets t)
    (hs : ∀ i, (jets.getD i zeroJet).DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hcc : Accepted center centerInputs) (hwc : Accepted whole wholeInputs)
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz)
    (ht : 0<BivariateJetEnclosure.taylorLower
      ((finalBoxes center centerInputs).getD i (zeroBox p)).toReal
      ((finalBoxes whole wholeInputs).getD i (zeroBox q)).toReal ra rz) :
    0<((finalJets whole jets).getD i zeroJet).value 1 := by sorry
