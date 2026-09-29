-- Prove2me | Theorems.Thm_LopesQM_dispersion_eq_zero_iff_eigenfunction
-- name    : LopesQM.dispersion_eq_zero_iff_eigenfunction
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T02:56:08.694771+00:00
-- url     : https://prove2.me/theorems/43c9147c-5f6d-4463-82c1-dc1da95b0522
-- title:
--   Proposição 8.1 — $\Delta_\psi(A)=0$ iff $\psi$ is an eigenfunction of $A$
-- statement:
--   Let $A$ be an operator on functions $\mathbb R^n\to\mathbb C$ and let $\psi\in L^2(\mathbb R^n)$ with $A\psi\in L^2(\mathbb R^n)$ and $|\psi|\ne 0$. Then
--   $$\Delta_\psi(A)=0\iff\exists\,\alpha\in\mathbb C:\;A\psi=\alpha\,\psi\ \text{ almost everywhere}.$$
--
--   States of zero dispersion are exactly the eigenstates: measuring $A$ in such a state returns the eigenvalue with certainty. This is the book's justification of the measurement postulate and the degenerate case of the uncertainty principle.
--
--   **Formalization Note** The book states the proposition for an observable (self-adjoint) $A$; with the convention $E_\psi(A)=\langle A\psi,\psi\rangle/\langle\psi,\psi\rangle$ adopted in the definitions, self-adjointness is not needed and is not assumed, so the statement is at least as strong as the book's. Equality of $L^2$ elements is equality almost everywhere.
-- source:
--   A. O. Lopes, "Uma Breve Introdução à Matemática da Mecânica Quântica", 31º Colóquio Brasileiro de Matemática, IMPA, 2017 (http://mat.ufrgs.br/~alopes/hom/livroquantum.pdf is the extended version); Proposição 8.1, p. 129 (Definições 8.1–8.2, pp. 125–128).

import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory

namespace LopesQM
theorem dispersion_eq_zero_iff_eigenfunction {n : ℕ} (A : Op n) (ψ : WaveFn n)
    (hψ : MemLp ψ 2) (hAψ : MemLp (A ψ) 2) (hne : l2Norm ψ ≠ 0) :
    dispersion A ψ = 0 ↔ ∃ α : ℂ, A ψ =ᵐ[volume] fun x => α * ψ x := by sorry
end LopesQM
