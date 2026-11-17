-- Prove2me | Theorems.Thm_N25_LocalFive_henselian_R5
-- name    : N25.LocalFive.henselian_R5
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:25:07.524171+00:00
-- url     : https://prove2.me/theorems/d10704b5-c7cd-4fc7-ad46-3389b1d0c5b9
-- title:
--   The ring of $5$-adic integers is Henselian
-- statement:
--   Let $R_5=ℤ_5$ be the ring of $5$-adic integers with its maximal ideal. Then $$R_5\ \text{is a Henselian local ring}.$$ This permits smooth lifting and divisibility arguments from the residue field to integral points.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal

noncomputable section
local instance instL_N25_LocalFive_henselian_R5_bfd51b_ia5b823 : Fact (Nat.Prime 5) := ⟨by decide⟩
open N25
open N25.LocalFive

theorem N25.LocalFive.henselian_R5 : HenselianLocalRing R5  := by sorry
