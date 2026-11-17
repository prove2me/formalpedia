-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientAction_isCusp25_iff
-- name    : MazurProof.RationalPointsN25QuotientAction.isCusp25_iff
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:55.915409+00:00
-- url     : https://prove2.me/theorems/fbf49ae5-7aee-4eac-a1d4-ef0478159ce1
-- title:
--   The canonical cusp locus consists exactly of five explicit projective points
-- statement:
--   Let $p$ be a canonical coordinate quadruple. Then $p$ is a cusp if and only if it is projectively equal to one of the five designated cusp points $A,B,C,D,E$: $$IsCusp_{25}(p)\iff p∼A∨p∼B∨p∼C∨p∼D∨p∼E.$$ This explicit classification is used to prove that source points are noncuspidal.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_RationalPointsN25QuotientAction

open MazurProof
open MazurProof.RationalPointsN25QuotientAction
open RationalPointsN25CanonicalPoints

theorem MazurProof.RationalPointsN25QuotientAction.isCusp25_iff (p : Coordinates25) :
    IsCusp25 p ↔
      ProjectivelyEqual25 p cusp25A ∨
      ProjectivelyEqual25 p cusp25B ∨
      ProjectivelyEqual25 p cusp25C ∨
      ProjectivelyEqual25 p cusp25D ∨
      ProjectivelyEqual25 p cusp25E := by sorry
