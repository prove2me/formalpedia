-- Prove2me | Theorems.Thm_Height_logHeight_algebraMap
-- name    : Height.logHeight_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/52d595cd-f0d6-55e8-8b2f-cc8b87221c1b
-- title:
--   Logarithmic height multiplies by [L:K] under extension
-- statement:
--   Let $K$ and $L$ be fields, each equipped with a number-field structure, with $L$ an algebra over $K$, and let $\iota$ be a finite index type. For any family $x : \iota \to K$, the assertion is that the logarithmic height of the family obtained by applying the structure map $K \to L$ componentwise, i.e. $i \mapsto \mathrm{algebraMap}_{K,L}(x_i)$, computed in $L$, equals $[L:K]$ times the logarithmic height of $x$ computed in $K$, where the degree $[L:K] = \mathrm{finrank}_K L$ is coerced to a real number and the equality is an equality of real numbers. Here `logHeight` is the logarithmic height of a finite tuple relative to its ambient number field, normalised as a sum over all places with their local degrees and not divided by the absolute degree of the field; it is this normalisation that accounts for the factor $[L:K]$ rather than invariance.
--
--   This is the standard behaviour of the relative (non-normalised) height of a tuple under extension of the ground number field, the statement which underlies the fact that the absolute height, obtained after dividing by the degree, is independent of the field in which the coordinates are taken. It is used in the bound [`Height.mulHeightBound_map_le`](thm.html#Height.mulHeightBound_map_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Height_logHeight_algebraMap.lean

import Mathlib.NumberTheory.Height.NumberField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Height.logHeight_algebraMap {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {ι : Type*} [Finite ι] (x : ι → K) :
    logHeight (fun i => algebraMap K L (x i))
      = (Module.finrank K L : ℝ) * logHeight x := by sorry
