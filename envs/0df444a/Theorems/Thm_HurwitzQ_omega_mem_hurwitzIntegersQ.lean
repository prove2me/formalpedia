-- Prove2me | Theorems.Thm_HurwitzQ_omega_mem_hurwitzIntegersQ
-- name    : HurwitzQ.omega_mem_hurwitzIntegersQ
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-18T18:09:32.073516+00:00
-- url     : https://prove2.me/theorems/f8a34c2e-7710-4623-af82-f5caef68d707
-- title:
--   The half-integral generator is a Hurwitz integer
-- statement:
--   Let $\mathcal{H}$ be the Hurwitz subring of the rational quaternions: the four coordinates of an element are either all in $\mathbb{Z}$ or all in $\mathbb{Z}+\frac12$. Put $\omega=(1+i+j+k)/2$, where $i,j,k$ are the standard quaternion units.
--
--   $$
--   \omega\in\mathcal{H}.
--   $$
--
--   This records membership of a standard generator in the coordinate-defined subring.
-- source:
--   Standard definition: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003, §5.1, The Hurwitz Integral Quaternions. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345 The displayed assertion is an elementary consequence of this definition; no numbered theorem attribution is claimed.

import Definitions.Def_HurwitzQ_hurwitzIntegersQ
import Definitions.Def_HurwitzQ_omega
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Tactic.Ring

open Quaternion QuaternionAlgebra HurwitzQ

theorem HurwitzQ.omega_mem_hurwitzIntegersQ : omega ∈ hurwitzIntegersQ := by sorry
