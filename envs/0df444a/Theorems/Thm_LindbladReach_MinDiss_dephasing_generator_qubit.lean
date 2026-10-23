-- Prove2me | Theorems.Thm_LindbladReach_MinDiss_dephasing_generator_qubit
-- name    : LindbladReach.MinDiss.dephasing_generator_qubit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:41.161545+00:00
-- url     : https://prove2.me/theorems/51662bc4-1b36-45a7-b8a5-913331c7be2a
-- title:
--   Proof of Lemma 2.11(ii), p. 8 — L_Z = 4(E∞ − id) and e^{tL_Z} → E∞ on one qubit (middle term corrected)
-- statement:
--   On one qubit let $Z=\operatorname{diag}(1,-1)$ and let $E_\infty$ be the projection onto the diagonal,
--   $$E_\infty\begin{bmatrix}\rho_{00}&\rho_{01}\\ \rho_{10}&\rho_{11}\end{bmatrix}=\begin{bmatrix}\rho_{00}&0\\ 0&\rho_{11}\end{bmatrix}.$$
--   With $L_Z(\rho)=2Z\rho Z-Z^*Z\rho-\rho Z^*Z$:
--
--   1. the generator is a multiple of $E_\infty-\mathrm{id}$:
--   $$L_Z=4\,(E_\infty-\mathrm{id});$$
--   2. the dephasing semigroup converges to the pinching:
--   $$\lim_{t\to\infty}e^{tL_Z}=E_\infty .$$
--
--   This shows that the conditional expectation $E_\infty$, which is not itself of the form $e^{tL}$, is a limit of dephasing semigroups. It therefore lies in every closed class that contains them.
--
--   **Formalization Note** The page writes $L_Z(\rho)=2Z\rho Z-\rho=4\big(\tfrac{\rho+Z\rho Z}{2}-\rho\big)=4(E_\infty-\mathrm{id})(\rho)$. Since $Z^*Z=I$, $L_Z(\rho)=2Z\rho Z-2\rho$, so the middle term "$2Z\rho Z-\rho$" is a slip. The outer identity, which the proof uses, is the one posed. The limit is in the operator-norm topology of superoperators.
-- source:
--   Cai, Govindarajan, Junge, How Far do Lindbladians Go?, arXiv:2504.04883v2, p. 8, proof of Lemma 2.11(ii); E∞ defined on p. 7

import Mathlib
import Definitions.Def_LindbladReach_MinDiss_Setting

namespace LindbladReach.MinDiss

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

/-- Proof of Lemma 2.11(ii), p. 8: on one qubit `L_Z = 4(E∞ − id)` and `e^{tL_Z} → E∞`
as `t → ∞`, with `Z = diag(1, −1)` and `E∞` the diagonal projection. -/
theorem dephasing_generator_qubit :
    dissipator (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) = (4 : ℂ) • (pinchAll - 1) ∧
      Filter.Tendsto
        (fun t : ℝ => NormedSpace.exp ((t : ℂ) • dissipator (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ)))
        Filter.atTop (nhds pinchAll) := by sorry

end LindbladReach.MinDiss
