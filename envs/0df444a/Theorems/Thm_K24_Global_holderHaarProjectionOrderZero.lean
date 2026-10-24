-- Prove2me | Theorems.Thm_K24_Global_holderHaarProjectionOrderZero
-- name    : K24.Global.holderHaarProjectionOrderZero
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:40:42.366153+00:00
-- url     : https://prove2.me/theorems/372231d5-565b-40cb-87f8-7f60a98f457c
-- title:
--   K24: zero-order Hölder Haar projections with the exact norm bounds
-- statement:
--   The public theorem has precisely this canonical boundary: on any
--   smooth four-manifold M, for a canonical bounded local cover C, nonnegative
--   alpha and H with 0 < alpha, and the genuine smooth circle action rho,
--   `HolderActionControl C alpha H 0 rho` implies
--   `HolderProjectionConclusions C alpha H 0 rho`.
--
--   All tensor, covector, and vector clauses of the canonical conclusion structure
--   are included. Each original order-zero Holder section is genuinely Haar
--   integrable. Its literal Pi0 and PiPerp have original BigHolder order-zero
--   regularity and finite original cover norm. Pi0 is invariant and idempotent,
--   and PiPerp has zero Haar average. The extended norm bounds are exactly H times
--   the original norm for Pi0, and (1+H) times it for PiPerp.
--
--   This is the entire canonical order-zero Holder projection bundle from the
--   original action-control hypothesis, with no new geometric or regularity
--   assumptions. It is stronger in exponent range than the original 0<alpha<1
--   applications because the proof only needs alpha>0.
--
--   The original root aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 and FullK24Statement
--   remain open. In particular this result does not establish the higher-order
--   Holder projection estimates needed at orders 2 and 3, Sobolev projections,
--   remaining differential/inverse estimates, or flat-torus sharpness. No claim
--   of norm continuity of the action on big Holder spaces is made.
--
--   Supporting original full target https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §1 common normalized Haar projection; the complete order-zero instance of HolderProjectionConclusions under HolderActionControl in canonical definition 9140e2e8-3049-4225-86fe-cfe1a8c49825.

import Definitions.Def_K24GlobalStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open K24.Global
open scoped Manifold ContDiff NNReal
universe u

theorem K24.Global.holderHaarProjectionOrderZero {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (α H : ℝ≥0) (hα : 0 < α)
    (rho : CircleAction M) :
    HolderActionControl C α H 0 rho → HolderProjectionConclusions C α H 0 rho := by sorry
