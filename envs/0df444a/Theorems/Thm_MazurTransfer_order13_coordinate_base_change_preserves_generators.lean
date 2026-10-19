-- Prove2me | Theorems.Thm_MazurTransfer_order13_coordinate_base_change_preserves_generators
-- name    : MazurTransfer.order13_coordinate_base_change_preserves_generators
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T03:03:52.099997+00:00
-- url     : https://prove2.me/theorems/c7f53693-2465-4d18-bd2c-2e3ec43ec57f
-- title:
--   The actual quadratic chart base-change maps preserve all four coordinates
-- statement:
--   Let $R$ and $S$ be commutative rings with an $R$-algebra structure on $S$. Let $e_A$ and $e_B$ be the specified scalar-extension isomorphisms for the ordinary and reciprocal quadratic coordinate algebras of the order-thirteen curve. They preserve their four coordinate generators:
--   $$e_A(1\otimes x_R)=x_S,\quad e_A(1\otimes y_R)=y_S,\quad e_B(1\otimes z_R)=z_S,\quad e_B(1\otimes w_R)=w_S.$$
--
--   These identities identify the concrete maps on the actual chart coordinates. They allow the chart maps to extend through the overlap localizations and prove compatibility with the reciprocal transition in the Cartesian base-change construction.
-- source:
--   The four checked generator equalities in MazurTheorem Order13CoordinateBaseChangeGenerators.lean, lines 41–95, with their original quadratic-coordinate helper proofs. Declaration and reference spans come from the Lean syntax oracles; proof bodies are unchanged, helpers are private, and the new conclusion is their conjunction. Vas and contributors, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13CoordinateAlgebraBaseChange
open MazurTransfer.Order13CoordinateBaseChange
open Algebra TensorProduct
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
universe u v

theorem MazurTransfer.order13_coordinate_base_change_preserves_generators (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] :
    ordinaryCoordinateRingEquiv R S (1 ⊗ₜ[R] xCoordinate R) = xCoordinate S ∧
    ordinaryCoordinateRingEquiv R S (1 ⊗ₜ[R] yCoordinate R) = yCoordinate S ∧
    reciprocalCoordinateRingEquiv R S (1 ⊗ₜ[R] zCoordinate R) = zCoordinate S ∧
    reciprocalCoordinateRingEquiv R S (1 ⊗ₜ[R] wCoordinate R) = wCoordinate S  := by sorry
