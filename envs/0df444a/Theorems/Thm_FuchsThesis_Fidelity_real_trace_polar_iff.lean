-- Prove2me | Theorems.Thm_FuchsThesis_Fidelity_real_trace_polar_iff
-- name    : FuchsThesis.Fidelity.real_trace_polar_iff
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-25T20:04:39.681064+00:00
-- url     : https://prove2.me/theorems/62158fa8-2ec9-4b22-a6aa-04697957eb57
-- title:
--   Equality in the real unitary trace bound is equivalent to positive polar alignment
-- statement:
--   Let $A$ be any complex square matrix on a finite-dimensional Hilbert space and let $U$ be unitary. Then
--
--   $$\operatorname{Re}\operatorname{Tr}(UA)=\operatorname{Tr}\sqrt{A^*A}\quad\Longleftrightarrow\quad UA=\sqrt{A^*A}.$$
--
--   This characterizes equality for the real unitary trace maximum, including singular matrices. The modulus maximum allows an arbitrary phase, so the distinction is necessary in applications to optimal quantum measurements.
-- source:
--   C. A. Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, printed p. 53 / PDF p. 62, Equations (3.60)–(3.62). The equality characterization is for the real trace maximum, as distinguished from the modulus maximum.

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.UnitaryGroup
open Matrix
open scoped MatrixOrder ComplexOrder

theorem FuchsThesis.Fidelity.real_trace_polar_iff {n : Type} [Fintype n] [DecidableEq n] (A U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    (U*A).trace.re=(CFC.sqrt (Aᴴ*A)).trace.re ↔ U*A=CFC.sqrt (Aᴴ*A) := by sorry
