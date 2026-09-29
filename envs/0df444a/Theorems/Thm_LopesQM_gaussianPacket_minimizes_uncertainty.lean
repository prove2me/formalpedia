-- Prove2me | Theorems.Thm_LopesQM_gaussianPacket_minimizes_uncertainty
-- name    : LopesQM.gaussianPacket_minimizes_uncertainty
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T02:56:49.050743+00:00
-- url     : https://prove2.me/theorems/e671c1b3-d275-4fd6-b5b2-6326a94ec512
-- title:
--   Definição 8.3 / p. 133 — the Gaussian packet attains $\Delta X_j\,\Delta P_j=\hbar/2$
-- statement:
--   Let $\hbar>0$, $a>0$, $x_0,p_0\in\mathbb R^n$ and $j\in\{1,\dots,n\}$, and let
--   $$\psi(x)=\frac{1}{(2\pi a^2)^{n/4}}\;e^{-\frac{|x-x_0|^2}{4a^2}}\;e^{\frac{i}{\hbar}\langle p_0,x\rangle}$$
--   be the Gaussian wave packet. Then:
--
--   1. $\psi$ is a state: $|\psi|=1$;
--   2. $E_\psi(X_j)=(x_0)_j$;
--   3. $E_\psi(P_j)=(p_0)_j$;
--   4. $\Delta_\psi(X_j)=a$;
--   5. $\Delta_\psi(X_j)\,\Delta_\psi(P_j)=\dfrac{\hbar}{2}$.
--
--   Together with Heisenberg's inequality this shows that the constant $\hbar/2$ is optimal and that Gaussian packets are minimal-uncertainty states, the quantum description of a particle localized at $x_0$ with momentum $p_0$.
--
--   **Formalization Note** The book writes $\Delta(X)$, $E(X)$, $E(P)$ for the vector position/momentum; the statement is formalized for each coordinate $j$. The Gaussian packet is not compactly supported, so it lies outside the book's domain $D(P_j)$; the momentum operator is nevertheless applied to it through the classical derivative, which is how the book computes these quantities.
-- source:
--   A. O. Lopes, "Uma Breve Introdução à Matemática da Mecânica Quântica", 31º Colóquio Brasileiro de Matemática, IMPA, 2017 (http://mat.ufrgs.br/~alopes/hom/livroquantum.pdf is the extended version); Definição 8.3 and the text following it, p. 133: 'O pacote de ondas gaussiano satisfaz as seguintes propriedades: Δ(X) = a, E(X) = x_0, E(P) = p_0 ... Estes estados minimizam a relação de incerteza de Heisenberg ... vale a relação Δ(X) Δ(P) = ħ/2.'

import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory

namespace LopesQM
theorem gaussianPacket_minimizes_uncertainty {n : ℕ} (hbar : ℝ) (hhbar : 0 < hbar)
    (a : ℝ) (ha : 0 < a) (x0 p0 : Rn n) (j : Fin n) :
    l2Norm (gaussianPacket hbar a x0 p0) = 1 ∧
    expectation (positionOp j) (gaussianPacket hbar a x0 p0) = ((x0 j : ℝ) : ℂ) ∧
    expectation (momentumOp hbar j) (gaussianPacket hbar a x0 p0) = ((p0 j : ℝ) : ℂ) ∧
    dispersion (positionOp j) (gaussianPacket hbar a x0 p0) = a ∧
    dispersion (positionOp j) (gaussianPacket hbar a x0 p0) *
      dispersion (momentumOp hbar j) (gaussianPacket hbar a x0 p0) = hbar / 2 := by sorry
end LopesQM
