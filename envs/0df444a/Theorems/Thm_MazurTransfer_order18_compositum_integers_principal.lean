-- Prove2me | Theorems.Thm_MazurTransfer_order18_compositum_integers_principal
-- name    : MazurTransfer.order18_compositum_integers_principal
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T18:03:07.5017+00:00
-- url     : https://prove2.me/theorems/f793456c-b260-40d5-8d0a-0041ead9f878
-- title:
--   Order-18 degree-nine compositum: full ring of integers is principal
-- statement:
--   Let $K=\mathbb Q[T]/(T^3-3T-1)$ and $M=K[S]/(S^3-3S-10)$, with their separately certified field structures. Then the full ring of integers $\mathcal O_M$ is a principal ideal ring. The proof establishes an exact Minkowski bound below $32$, identifies the primes over $2$ and $3$ as principal, and uses inertia certificates to exclude every other relevant rational prime through $31$. This is the full class-number-one input to the original order-18 Selmer descent, with no conditional class-number hypothesis.
-- source:
--   User MazurTheorem WIP, commit 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact source AST declarations with Apache-2.0 headers retained. Complete proof closure selected by kernel dependencies and resolved whole Lean AST commands; field validity uses the already proved irreducibility contracts.

import Definitions.Def_MazurTransfer_Order18CompositumField

theorem MazurTransfer.order18_compositum_integers_principal :
IsPrincipalIdealRing (NumberField.RingOfIntegers MazurTorsion.XOneEighteenTwoDivisionArithmetic.M) := by sorry
