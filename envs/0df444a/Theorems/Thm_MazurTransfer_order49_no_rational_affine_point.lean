-- Prove2me | Theorems.Thm_MazurTransfer_order49_no_rational_affine_point
-- name    : MazurTransfer.order49_no_rational_affine_point
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T05:56:54.129831+00:00
-- url     : https://prove2.me/theorems/b4948ce2-8182-46c8-9609-54d1bb3684f0
-- title:
--   No rational point of exact order 49 on any elliptic curve over Q
-- statement:
--   For every elliptic curve $E/\mathbb Q$ and every rational affine group point $P\in E(\mathbb Q)$, $$\operatorname{ord}(P)\ne49.$$ Ellipticity is the only curve hypothesis. The statement also covers points of infinite order and does not assume finiteness of the rational torsion group.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 original headers and attribution retained. Exact original rationalPoint_addOrderOf_ne_fortyNine proof selected at original kernel dependencies and complete Lean AST source ranges. Reuses the Proved plane obstruction, official Anthropic FLT division-polynomial interface, all separately Proved point-map and residual-Hauptmodul helpers, the exact conditional G7F contract and the separately registered bounded-resultant contract. All original kernel and resultant conditions are discharged internally; ellipticity is the only public curve hypothesis. No new hypothesis, changed coefficient, custom axiom, resource-strengthening option or altered final statement. Named downstream consumer: MazurCampaign.no_order_forty_nine and the full Mazur classification.

import Mathlib

theorem MazurTransfer.order49_no_rational_affine_point (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 49 := by sorry
