-- Prove2me | Theorems.Thm_OPG37364_psl2_complex_rep_finrank_lower_bound
-- name    : OPG37364.psl2_complex_rep_finrank_lower_bound
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T13:23:01.303642+00:00
-- url     : https://prove2.me/theorems/08f6bccb-777f-45c1-ae80-91b0e8683cb4
-- title:
--   Complex representation degrees of PSL₂ over a prime field
-- statement:
--   Let $q\ge5$ be prime, let $V$ be a finite-dimensional complex vector space, and let $\rho:\operatorname{PSL}_2(\mathbb F_q)\to\operatorname{GL}(V)$ be a nontrivial representation. Then
--
--   $$q-1\le2\dim_{\mathbb C}V.$$
--
--   Nontriviality means that some group element acts by an operator different from the identity. No irreducibility or faithfulness assumption is imposed; faithfulness follows from the existing simplicity theorem for PSL₂. A trivial action on a nonzero vector space is excluded.
--
--   This formalizes the classical Frobenius representation-degree lower bound presented in Davidoff–Sarnak–Valette, Theorem 3.5.1, in its finite-dimensional complex form. The proof uses the eigenvalue orbit of a unipotent element under diagonal conjugation. It contains no graph-existence or spectral-bound assumption.
-- source:
--   Davidoff, Sarnak and Valette, Elementary Number Theory, Group Theory, and Ramanujan Graphs, §3.5, Theorem 3.5.1 (printed p. 102; proof p. 106), the classical bound attributed to Frobenius. https://math.bme.hu/~gabor/oktatas/SztoM/DavidoffSarnakValette.pdf . This is a formalization of existing mathematics, not a novelty claim.

import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
set_option autoImplicit false
open scoped MatrixGroups
open Matrix Matrix.SpecialLinearGroup Module

namespace OPG37364

theorem psl2_complex_rep_finrank_lower_bound
    (q : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (PSL(2, ZMod q)) V) (hρ : ∃ g, ρ g ≠ 1) :
    q - 1 ≤ 2 * Module.finrank ℂ V := by sorry

end OPG37364
