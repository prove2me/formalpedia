-- Prove2me | Theorems.Thm_LopesQM_canonical_commutation_relations
-- name    : LopesQM.canonical_commutation_relations
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T02:42:52.081103+00:00
-- url     : https://prove2.me/theorems/e87b1f02-c97d-4bd6-beba-bf3bb0ecd8ca
-- title:
--   Lema 3.2 — canonical commutation relations $\frac{i}{\hbar}[P_j,X_j]=\mathrm{Id}$
-- statement:
--   Let $\hbar>0$ and $j,k\in\{1,\dots,n\}$, with $X_j$ the position and $P_j=-i\hbar\,\partial/\partial x_j$ the momentum operators on functions $\psi:\mathbb R^n\to\mathbb C$. Then, pointwise at every $x\in\mathbb R^n$:
--
--   1. $[X_k,X_j]\psi=0$ for every $\psi$;
--   2. $[P_k,P_j]\psi=0$ for every $\psi$ of class $C^2$;
--   3. for every differentiable $\psi$,
--   $$\frac{i}{\hbar}\,[P_j,X_j]\psi=\psi;$$
--   4. if $j\ne k$, then $\frac{i}{\hbar}[P_j,X_k]\psi=0$ for every differentiable $\psi$.
--
--   These are the canonical commutation relations, the quantum counterpart of the Poisson brackets $\{x_k,p_j\}=\delta_{kj}$; relation 3 is the identity that drives the proof of Heisenberg's uncertainty principle.
--
--   **Formalization Note** The book states the relations as operator identities and remarks that domain questions are glossed over; here each relation is stated pointwise for the smoothness class used in its proof ($C^2$ for relation 2, differentiability for 3 and 4).
-- source:
--   A. O. Lopes, "Uma Breve Introdução à Matemática da Mecânica Quântica", 31º Colóquio Brasileiro de Matemática, IMPA, 2017 (http://mat.ufrgs.br/~alopes/hom/livroquantum.pdf is the extended version); Lema 3.2, p. 65 (commutator: Definição 3.1, p. 64).

import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory

namespace LopesQM
theorem canonical_commutation_relations {n : ℕ} (hbar : ℝ) (hhbar : 0 < hbar) (j k : Fin n) :
    (∀ ψ : WaveFn n, ∀ x : Rn n,
        commutator (positionOp k) (positionOp j) ψ x = 0) ∧
    (∀ ψ : WaveFn n, ContDiff ℝ 2 ψ → ∀ x : Rn n,
        commutator (momentumOp hbar k) (momentumOp hbar j) ψ x = 0) ∧
    (∀ ψ : WaveFn n, Differentiable ℝ ψ → ∀ x : Rn n,
        Complex.I / (hbar : ℂ) * commutator (momentumOp hbar j) (positionOp j) ψ x = ψ x) ∧
    (j ≠ k → ∀ ψ : WaveFn n, Differentiable ℝ ψ → ∀ x : Rn n,
        Complex.I / (hbar : ℂ) * commutator (momentumOp hbar j) (positionOp k) ψ x = 0) := by sorry
end LopesQM
