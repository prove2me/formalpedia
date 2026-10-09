-- Prove2me | Theorems.Thm_HurwitzQ_lift_mem_hurwitzIntegers
-- name    : HurwitzQ.lift_mem_hurwitzIntegers
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-18T18:08:04.649966+00:00
-- url     : https://prove2.me/theorems/6ac88ebe-7112-496b-a7f6-4a7eff97fece
-- title:
--   Rational Hurwitz integers map into the real model
-- statement:
--   Let $\mathcal{H}$ be the Hurwitz subring of the rational quaternions: the four coordinates of an element are either all in $\mathbb{Z}$ or all in $\mathbb{Z}+\frac12$. Let $\iota$ apply the canonical inclusion $\mathbb{Q}\hookrightarrow\mathbb{R}$ to each quaternion coordinate, and let $\mathcal{H}_{\mathbb{R}}$ be the real-quaternion subring defined by the same coordinate condition. Let $q$ be a rational quaternion.
--
--   $$
--   q\in\mathcal{H}\implies\iota(q)\in\mathcal{H}_{\mathbb{R}}.
--   $$
--
--   This connects the rational and real realizations of the Hurwitz integers.
-- source:
--   Standard definition: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003, §5.1, The Hurwitz Integral Quaternions. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345 The displayed assertion is an elementary consequence of this definition; no numbered theorem attribution is claimed.

import Definitions.Def_HurwitzQ_hurwitzIntegersQ
import Definitions.Def_Quaternion_hurwitzIntegers
import Definitions.Def_Quaternion_lipschitzIntegers
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Quaternion QuaternionAlgebra HurwitzQ

theorem HurwitzQ.lift_mem_hurwitzIntegers {q : ℍ[ℚ]} (hq : q ∈ hurwitzIntegersQ) :
    (⟨(q.re : ℝ), (q.imI : ℝ), (q.imJ : ℝ), (q.imK : ℝ)⟩ : ℍ[ℝ]) ∈ hurwitzIntegers := by sorry
