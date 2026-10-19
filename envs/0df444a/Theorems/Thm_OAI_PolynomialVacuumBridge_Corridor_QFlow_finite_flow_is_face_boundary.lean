-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_QFlow_finite_flow_is_face_boundary
-- name    : OAI.PolynomialVacuumBridge.Corridor.QFlow.finite_flow_is_face_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:46:31.48265+00:00
-- url     : https://prove2.me/theorems/3c0a7596-7121-48c8-82fc-c58238bda3fb
-- title:
--   Finite rational honeycomb flows are boundaries of face potentials
-- statement:
--   Let $(q_0,q_1,q_2)$ be finitely supported functions $\mathbb Z^2\to\mathbb Q$ describing a flow on the three edge directions of the honeycomb lattice, conserved at up and down vertices:
--   $$
--   q_0(i,j)+q_1(i,j)+q_2(i,j)=0,\qquad q_0(i,j+1)+q_1(i,j)+q_2(i+1,j)=0 .
--   $$
--   Then there is a finitely supported face potential $p:\mathbb Z^2\to\mathbb Q$ with
--   $$
--   q_0(i,j)=p(i,j)-p(i-1,j),\quad q_1(i,j)=p(i-1,j+1)-p(i,j),\quad q_2(i,j)=p(i-1,j)-p(i-1,j+1).
--   $$
--
--   This is a discrete Poincaré lemma: every finite conserved flow on the planar honeycomb lattice is a sum of face circulations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/RationalPotential.lean#L170-L185

import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor OAI.PolynomialVacuumBridge.Corridor.QFlow

theorem OAI.PolynomialVacuumBridge.Corridor.QFlow.finite_flow_is_face_boundary (q : FiniteHoneycombFlow) :
    ∃ p : FaceIndex →₀ ℚ, ∀ i j,
      q.q0 (i,j) = p (i,j) - p (i-1,j) ∧
      q.q1 (i,j) = p (i-1,j+1) - p (i,j) ∧
      q.q2 (i,j) = p (i-1,j) - p (i-1,j+1) := by sorry
