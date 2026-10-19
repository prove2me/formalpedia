-- Prove2me | Theorems.Thm_MazurTransfer_Order13DiamondSexticSymmetry_transcendental_diamondX
-- name    : MazurTransfer.Order13DiamondSexticSymmetry.transcendental_diamondX
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T10:57:08.371977+00:00
-- url     : https://prove2.me/theorems/723331ff-b8c1-44a0-a513-bc1fc739e471
-- title:
--   The diamond fractional-linear coordinate preserves transcendence
-- statement:
--   Let $K$ and $F$ be fields, with $F$ a $K$-algebra. If $x\in F$ is transcendental over $K$, then so is its diamond coordinate $$d_X(x)=-\frac1{x+1}.$$ No denominator condition is supplied: transcendence itself implies $x+1\ne0$. This gives the injectivity input for the actual diamond map on the ordinary coordinate ring.
-- source:
--   Original complete transcendental_diamondX statement and proof body from MazurTheorem Order13DiamondSexticSymmetry.lean, Apache-2.0, Vas and contributors. The original implicit field context and both universe declarations are retained; only the top-level solution name and public coordinate-transform import change. Full original and public closed types are kernel-compared. Native, strict and complete frontend checks pass with standard axioms only. Named downstream consumer: the actual rational diamond coordinate-ring injection and function-field automorphism.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Original MazurTheorem diamond-coordinate transcendence argument.
Design boundary: the diamond rational coordinate of a transcendental element
is transcendental over the same coefficient field.
Named downstream consumer: actual diamond coordinate-ring injection. -/
import Definitions.Def_MazurTransfer_Order13DiamondSexticCoordinateTransform
noncomputable section
universe u v
open MazurTransfer.Order13DiamondSexticSymmetry
variable {F : Type u} [Field F]

theorem MazurTransfer.Order13DiamondSexticSymmetry.transcendental_diamondX (K : Type v) [Field K] [Algebra K F]
    (x : F) (hx : Transcendental K x) : Transcendental K (diamondX x) := by sorry
