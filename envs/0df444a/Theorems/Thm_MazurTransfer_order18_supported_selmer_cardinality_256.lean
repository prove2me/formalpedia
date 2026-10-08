-- Prove2me | Theorems.Thm_MazurTransfer_order18_supported_selmer_cardinality_256
-- name    : MazurTransfer.order18_supported_selmer_cardinality_256
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T19:05:09.511988+00:00
-- url     : https://prove2.me/theorems/c7fc4eca-0000-4c27-87cf-e37e2179a775
-- title:
--   Order-18 supported ambient square classes: exact cardinality 256
-- statement:
--   Let $K$ be the original cubic coefficient field, $M/K$ the original relative two-division field of absolute degree nine, and $\mathcal R$ the integral closure of $\mathcal O_K$ in $M$. Let $S$ be the primes of $\mathcal R$ above the dyadic primes of $K$. Define $M(S,2)$ to be the square classes in $M^\times/(M^\times)^2$ whose valuations are even at every prime outside $S$. Then
--
--   $$
--   |M(S,2)|=256.
--   $$
--
--   This is the exact cardinality of the supported ambient square-class group used in the order-18 descent. It imposes no principal-ring, unit-cardinality or valuation-certificate hypothesis. The relative norm kernel, its representative classification and the elliptic-curve local images are separate arithmetic results.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, original MazurTorsion.XOneEighteenGlobalSelmerBridge.natCard_dyadicSelmerM, XOneEighteenGlobalSelmerBridge.lean lines505-537. The original square-class group, dyadic support and generic cardinality proof are retained by resolved Lean AST commands. The original principal-ring and valuation-certificate hypotheses are discharged with independently public Proved results; signature and unit-index calculations reuse their exact public contracts. Apache-2.0 headers/authors preserved. Named downstream consumer: the original 16-element norm-kernel and representative classification.

import Definitions.Def_MazurTransfer_Order18AmbientSelmer

theorem MazurTransfer.order18_supported_selmer_cardinality_256 :
Nat.card MazurTorsion.XOneEighteenGlobalSelmerBridge.DyadicSelmerM = 256 := by sorry
