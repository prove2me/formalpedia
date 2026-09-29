-- Prove2me | Theorems.Thm_LopesQM_heisenberg_uncertainty
-- name    : LopesQM.heisenberg_uncertainty
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T02:57:21.903287+00:00
-- url     : https://prove2.me/theorems/e3908941-c136-4843-b643-e27f6e69980a
-- title:
--   Teorema 8.2 — Heisenberg's uncertainty principle $\Delta X_j\,\Delta P_j\ge\hbar/2$
-- statement:
--   Let $\hbar>0$ be Planck's constant, $j\in\{1,\dots,n\}$, and let $\psi:\mathbb R^n\to\mathbb C$ be a state (i.e. $|\psi|=1$) lying in $D(X_j)\cap D(P_j)$: $\psi$ and $x_j\psi$ are square integrable, and $\psi$ is of class $C^1$ with compact support. Then the dispersions of the position operator $X_j$ and the momentum operator $P_j=-i\hbar\,\partial/\partial x_j$ in the state $\psi$ satisfy
--   $$\Delta_\psi(X_j)\;\Delta_\psi(P_j)\;\ge\;\frac{\hbar}{2}.$$
--
--   This is Heisenberg's uncertainty principle: no state can have position $x_j$ and momentum $p_j$ both sharply concentrated. It is the capstone of Chapter 8 of the book.
--
--   **Formalization Note** $D(P_j)$ is the book's domain of compactly supported $C^1$ functions (Definição 1.20); the condition $\psi\in D(X_j)$ is then automatic but is kept as in the book. Dispersion is $\Delta_\psi(A)=|(A-E_\psi(A)I)\psi|$ with $E_\psi(A)=\langle A\psi,\psi\rangle/\langle\psi,\psi\rangle$.
-- source:
--   A. O. Lopes, "Uma Breve Introdução à Matemática da Mecânica Quântica", 31º Colóquio Brasileiro de Matemática, IMPA, 2017 (http://mat.ufrgs.br/~alopes/hom/livroquantum.pdf is the extended version); Teorema 8.2 (Princípio da incerteza de Heisenberg), p. 131; Definições 8.1–8.2 (pp. 125–128), Definição 1.20 and D(X_j), D(P_j) (pp. 23–25).

import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory

namespace LopesQM
theorem heisenberg_uncertainty {n : ℕ} (hbar : ℝ) (hhbar : 0 < hbar) (j : Fin n)
    (ψ : WaveFn n) (hX : InPositionDomain j ψ) (hP : InMomentumDomain ψ)
    (hnorm : l2Norm ψ = 1) :
    dispersion (positionOp j) ψ * dispersion (momentumOp hbar j) ψ ≥ hbar / 2 := by sorry
end LopesQM
