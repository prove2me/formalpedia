-- Prove2me | Theorems.Thm_LesHouchesWidth_gaussPairAvg_relu
-- name    : LesHouchesWidth.gaussPairAvg_relu
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:08:03.161692+00:00
-- url     : https://prove2.me/theorems/387e018e-351f-4951-96a3-c4b8e639a3bc
-- title:
--   Eq. (16): the ReLU Gaussian pair average (arc-cosine kernel)
-- statement:
--   Let $\Sigma=\begin{pmatrix}\Sigma_{11}&\Sigma_{12}\\\Sigma_{12}&\Sigma_{22}\end{pmatrix}$ with $\Sigma_{11}>0$, $\Sigma_{22}>0$ and $\Sigma_{12}^2\le\Sigma_{11}\Sigma_{22}$. For $\varphi(t)=\max(t,0)$,
--   $$F_{\mathrm{ReLU}}(\Sigma_{11},\Sigma_{12},\Sigma_{22})=\mathbb E_{(u_1,u_2)\sim\mathcal N(0,\Sigma)}[\varphi(u_1)\varphi(u_2)]=\frac{1}{2\pi}\sqrt{\Sigma_{11}\Sigma_{22}}\,\big[\sin\theta+(\pi-\theta)\cos\theta\big],\qquad \theta=\arccos\frac{\Sigma_{12}}{\sqrt{\Sigma_{11}\Sigma_{22}}}.$$
--
--   This makes the NNGP kernel recursion explicit for ReLU networks.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 5, eq. (16) (Lecture 1, Section 1.4), citing Cho–Saul (ref. [4] of the notes).

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem gaussPairAvg_relu (s11 s12 s22 : ℝ) (h11 : 0 < s11) (h22 : 0 < s22)
    (h12 : s12 ^ 2 ≤ s11 * s22) :
    gaussPairAvg (fun t => max t 0) s11 s12 s22 =
      1 / (2 * Real.pi) * Real.sqrt (s11 * s22) *
        (Real.sin (Real.arccos (s12 / Real.sqrt (s11 * s22))) +
          (Real.pi - Real.arccos (s12 / Real.sqrt (s11 * s22))) *
            Real.cos (Real.arccos (s12 / Real.sqrt (s11 * s22)))) := by sorry

end LesHouchesWidth
