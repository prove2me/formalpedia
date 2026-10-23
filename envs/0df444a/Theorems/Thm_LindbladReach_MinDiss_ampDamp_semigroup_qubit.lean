-- Prove2me | Theorems.Thm_LindbladReach_MinDiss_ampDamp_semigroup_qubit
-- name    : LindbladReach.MinDiss.ampDamp_semigroup_qubit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:41.406499+00:00
-- url     : https://prove2.me/theorems/7e18f736-a20b-4068-a9bb-428807618e67
-- title:
--   Proof of Lemma 2.11, p. 8 ([CW16]) — the amplitude-damping semigroup e^{tL_a}, a = |0⟩⟨1|, on one qubit
-- statement:
--   On one qubit, with basis $(|0\rangle,|1\rangle)$, let $a=|0\rangle\langle1|$ and $L_a(\rho)=2a\rho a^*-a^*a\rho-\rho a^*a$. For every real $t$ and every $2\times2$ complex matrix $\rho$,
--   $$e^{tL_a}\begin{bmatrix}\rho_{00}&\rho_{01}\\ \rho_{10}&\rho_{11}\end{bmatrix}=\begin{bmatrix}\rho_{00}+(1-e^{-2t})\rho_{11}&e^{-t}\rho_{01}\\ e^{-t}\rho_{10}&e^{-2t}\rho_{11}\end{bmatrix}.$$
--
--   This is the closed form of the amplitude-damping semigroup. As $t\to\infty$ it tends to the reset channel $\rho\mapsto\operatorname{tr}(\rho)|0\rangle\langle0|$, and along the way it reaches every diagonal density from $|1\rangle\langle1|$.
--
--   **Formalization Note** The semigroup is the exponential of the superoperator $tL_a$. The page states the formula with no sign condition on $t$, and it holds for every real $t$. The dissipator has the standard sign, and with it the display is the paper's.
-- source:
--   Cai, Govindarajan, Junge, How Far do Lindbladians Go?, arXiv:2504.04883v2, p. 8, proof of Lemma 2.11, display quoted from [CW16]

import Mathlib
import Definitions.Def_LindbladReach_MinDiss_Setting

namespace LindbladReach.MinDiss

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

/-- Proof of Lemma 2.11, p. 8, quoting [CW16]: the amplitude-damping semigroup on one qubit,
`a = |0⟩⟨1|`, basis order `(|0⟩, |1⟩)`. -/
theorem ampDamp_semigroup_qubit (t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    NormedSpace.exp ((t : ℂ) • dissipator (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) ρ =
      !![ρ 0 0 + (1 - (Real.exp (-2 * t) : ℂ)) * ρ 1 1, (Real.exp (-t) : ℂ) * ρ 0 1;
         (Real.exp (-t) : ℂ) * ρ 1 0, (Real.exp (-2 * t) : ℂ) * ρ 1 1] := by sorry

end LindbladReach.MinDiss
