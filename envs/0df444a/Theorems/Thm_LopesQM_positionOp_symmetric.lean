-- Prove2me | Theorems.Thm_LopesQM_positionOp_symmetric
-- name    : LopesQM.positionOp_symmetric
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T02:46:03.02951+00:00
-- url     : https://prove2.me/theorems/ab91f078-0378-4389-beef-48dcad30d2de
-- title:
--   p. 23 — the position operator $X_j$ is symmetric on $D(X_j)$
-- statement:
--   Let $j\in\{1,\dots,n\}$ and let $\psi,\varphi\in D(X_j)$, i.e. $\psi,\varphi\in L^2(\mathbb R^n)$ and $x_j\psi,\;x_j\varphi\in L^2(\mathbb R^n)$. Then
--   $$\langle X_j\psi,\varphi\rangle=\langle\psi,X_j\varphi\rangle,\qquad\text{i.e.}\qquad \int_{\mathbb R^n}x_j\,\psi(x)\,\overline{\varphi(x)}\,dx=\int_{\mathbb R^n}\psi(x)\,\overline{x_j\,\varphi(x)}\,dx.$$
--
--   Symmetry of the position operator is used whenever $\langle\psi,X_jA\psi\rangle$ is rewritten as $\langle X_j\psi,A\psi\rangle$, in particular in the proof of the uncertainty principle and to see that $E_\psi(X_j)$ is real.
-- source:
--   A. O. Lopes, "Uma Breve Introdução à Matemática da Mecânica Quântica", 31º Colóquio Brasileiro de Matemática, IMPA, 2017 (http://mat.ufrgs.br/~alopes/hom/livroquantum.pdf is the extended version); Chapter 1, example 2) of operators (multiplication by a coordinate), pp. 22–23: '< X_j ψ, φ > = < ψ, X_j φ >. Logo X_j é autoadjunto.'

import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory

namespace LopesQM
theorem positionOp_symmetric {n : ℕ} (j : Fin n) (ψ φ : WaveFn n)
    (hψ : InPositionDomain j ψ) (hφ : InPositionDomain j φ) :
    l2Inner (positionOp j ψ) φ = l2Inner ψ (positionOp j φ) := by sorry
end LopesQM
