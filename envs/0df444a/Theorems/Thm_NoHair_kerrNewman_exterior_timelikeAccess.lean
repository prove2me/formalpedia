-- Prove2me | Theorems.Thm_NoHair_kerrNewman_exterior_timelikeAccess
-- name    : NoHair.kerrNewman_exterior_timelikeAccess
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T20:31:45.728804+00:00
-- url     : https://prove2.me/theorems/4c5fbcdb-8360-4df5-aa4f-f302e59c0985
-- title:
--   Exterior Kerr–Newman points can send and receive timelike signals from arbitrarily large radii
-- statement:
--   Fix an arbitrary Cartesian cutoff $R$. Every event with $r>r_+$ can send and receive timelike signals to or from events with spatial radius exceeding $R$, using the canonical ingoing Kerr–Schild time orientation. The statement includes the rotation axis and extremal parameters.
-- source:
--   W. Hasse and V. Perlick, A Morse-theoretical analysis of gravitational lensing by a Kerr–Newman black hole, https://arxiv.org/abs/gr-qc/0511135, section III, Eqs. (8)–(12).

import Definitions.Def_NoHair_kerrNewmanTimeDirection

open scoped ContDiff Manifold
open NoHair Set

theorem NoHair.kerrNewman_exterior_timelikeAccess (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) (R : ℝ) :
    let A := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' exteriorRegion R
    let D := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a e
    let T := kerrNewmanTimeDirection m a e
    let g := kerrNewmanMetricField m a e
    D ⊆ chronoPastSet g T A ∩ chronoFutureSet g T A := by sorry
