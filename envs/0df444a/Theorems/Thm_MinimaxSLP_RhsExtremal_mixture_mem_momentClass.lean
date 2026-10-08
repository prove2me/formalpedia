-- Prove2me | Theorems.Thm_MinimaxSLP_RhsExtremal_mixture_mem_momentClass
-- name    : MinimaxSLP.RhsExtremal.mixture_mem_momentClass
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:24.521968+00:00
-- url     : https://prove2.me/theorems/cbdbefde-e667-4ba4-a448-467abb2b9c88
-- title:
--   Proof of Theorem 3.3, pp. 590–591 — the Gaussian mixture P_m(x) has mean μ and second moment Q
-- statement:
--   Let $(V_k^i,v_k^i,v_{k0}^i)_{k=1,\dots,K,\ i=1,\dots,N}$ be a feasible point of (16) in which every block has $v_{k0}^i>0$ or is zero. Let $P_m(x)$ be the mixed distribution that, with probability $v_{k0}^i$, draws
--   $$
--   \tilde h_k^i\sim\mathbb N\!\left(\frac{v_k^i}{v_{k0}^i},\ \frac{V_k^i v_{k0}^i-v_k^i(v_k^i)'}{(v_{k0}^i)^2}\right).
--   $$
--   Then $P_m(x)$ is a probability distribution with finite second moments and
--   $$
--   \mathbb E_{P_m(x)}[\tilde h]=\mu,\qquad \mathbb E_{P_m(x)}[\tilde h\tilde h']=Q,
--   $$
--   i.e. $P_m(x)\in\mathcal P$.
--
--   This is the moment-matching step of the construction of the extremal distribution.
--
--   **Formalization Note** The normal components are Mathlib's `multivariateGaussian` (which accepts singular positive semidefinite covariances), transported from `EuclideanSpace ℝ (Fin r)` to `Fin r → ℝ`; weights are `ENNReal.ofReal` $v_{k0}^i$. The paper's "$V_k^iv_{k0}$", "$v_{k0}^2$" and "with probability $v_{k0}$" are read with the superscript $i$.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, pp. 590–591, proof of Theorem 3.3

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_RhsExtremal_Model

namespace MinimaxSLP.RhsExtremal

open MeasureTheory Matrix

/-- Proof of Theorem 3.3, pp. 590–591: if `s` is feasible for (16) and every block has
`v_k0^i > 0` or is zero, the mixture `P_m(x)` that draws `h̃_k^i ∼ ℕ(v_k^i/v_k0^i,
(V_k^i v_k0^i − v_k^i (v_k^i)′)/(v_k0^i)²)` with probability `v_k0^i` lies in `𝒫`:
`E[h̃] = μ` and `E[h̃h̃′] = Q`. -/
theorem mixture_mem_momentClass {r K N : ℕ} (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (s : Fin K → Fin N → (Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ))
    (hs : s ∈ feasible16 K N μ Q)
    (hpos : ∀ k i, 0 < (s k i).2.2 ∨ s k i = 0) :
    mixture s ∈ MinimaxSLP.ObjSDP.momentClass μ Q := by sorry

end MinimaxSLP.RhsExtremal
