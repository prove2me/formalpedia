-- Prove2me | Theorems.Thm_FuchsThesis_Fidelity_polar_attainer
-- name    : FuchsThesis.Fidelity.polar_attainer
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-25T20:04:37.484443+00:00
-- url     : https://prove2.me/theorems/3103bdff-b5d8-5b35-928c-e3a3b1f1c371
-- title:
--   A unitary polar factor attains the positive modulus for every square matrix
-- statement:
--   Let $A$ be any complex square matrix on a finite-dimensional Hilbert space, without an invertibility assumption. There exists a unitary $U$ satisfying
--
--   $$UA=\sqrt{A^*A}.$$
--
--   The square root is the unique positive semidefinite square root. This positive polar alignment supplies attainment in trace-norm variational formulas and in fidelity measurement bounds.
-- source:
--   C. A. Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, printed p. 53 / PDF p. 62, Equations (3.60)–(3.62). The equality characterization is for the real trace maximum, as distinguished from the modulus maximum.

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.UnitaryGroup
open Matrix
open scoped MatrixOrder ComplexOrder

theorem FuchsThesis.Fidelity.polar_attainer {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    ∃ U ∈ unitaryGroup n ℂ, U*A=CFC.sqrt (Aᴴ*A) := by sorry
