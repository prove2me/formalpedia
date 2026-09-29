-- Prove2me | Theorems.Thm_LopesQM_momentumOp_symmetric
-- name    : LopesQM.momentumOp_symmetric
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T02:54:11.33854+00:00
-- url     : https://prove2.me/theorems/4ea8e689-e923-458c-ae2f-a3df7e79afec
-- title:
--   pp. 26–27 — the momentum operator $P_j$ is symmetric on $D(P_j)$
-- statement:
--   Let $\hbar\in\mathbb R$, $j\in\{1,\dots,n\}$, and let $\psi,\varphi:\mathbb R^n\to\mathbb C$ be of class $C^1$ with compact support. Then
--   $$\langle P_j\psi,\varphi\rangle=\langle\psi,P_j\varphi\rangle,\qquad\text{i.e.}\qquad\int_{\mathbb R^n}\Big(-i\hbar\,\frac{\partial\psi}{\partial x_j}\Big)\overline{\varphi}\,dx=\int_{\mathbb R^n}\psi\,\overline{\Big(-i\hbar\,\frac{\partial\varphi}{\partial x_j}\Big)}\,dx.$$
--
--   This is the integration-by-parts identity behind the self-adjointness of the momentum observable; it is used to move $P_j$ across the inner product in the proof of the uncertainty principle.
--
--   **Formalization Note** The book proves the case $n=1$ explicitly and asserts the general case; the statement here is for arbitrary $n$ and arbitrary index $j$. The book's standing convention $\hbar>0$ is not needed and not imposed.
-- source:
--   A. O. Lopes, "Uma Breve Introdução à Matemática da Mecânica Quântica", 31º Colóquio Brasileiro de Matemática, IMPA, 2017 (http://mat.ufrgs.br/~alopes/hom/livroquantum.pdf is the extended version); Definição 1.20 and the discussion following it, pp. 24–27: 'para todo φ, ψ ∈ D(P_1) vale < P_1 ψ, φ > = < ψ, P_1 φ >. Logo, P_1 é simétrico. Da mesma forma se mostra que P_j ...'

import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory

namespace LopesQM
theorem momentumOp_symmetric {n : ℕ} (hbar : ℝ) (j : Fin n) (ψ φ : WaveFn n)
    (hψ : InMomentumDomain ψ) (hφ : InMomentumDomain φ) :
    l2Inner (momentumOp hbar j ψ) φ = l2Inner ψ (momentumOp hbar j φ) := by sorry
end LopesQM
