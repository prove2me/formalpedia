-- Prove2me | Theorems.Thm_LesHouchesWidth_output_eq_sum_over_paths
-- name    : LesHouchesWidth.output_eq_sum_over_paths
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T21:59:08.565982+00:00
-- url     : https://prove2.me/theorems/c414b892-6380-4df5-8c71-bd069e02712f
-- title:
--   Eq. (123): sum-over-paths formula for a ReLU network
-- statement:
--   For every configuration of weights, every input $x\in\mathbb R^{n_0}$ and every output neuron $q$,
--   $$z^{(L+1)}_q(x)=\sum_{p=1}^{n_0}x_p\sum_{\gamma\in\Gamma_{p,q}}\Big(\prod_{\ell=1}^{L+1}W^{(\ell)}_{\gamma(\ell)\gamma(\ell-1)}\Big)\Big(\prod_{\ell=1}^{L}\xi^{(\ell)}_{\gamma;x}\Big),\qquad \xi^{(\ell)}_{\gamma;x}=\mathbf 1\{z^{(\ell)}_{\gamma(\ell)}(x)>0\},$$
--   where $\Gamma_{p,q}$ is the set of paths $\gamma=(\gamma(0),\dots,\gamma(L+1))$ through the network with $\gamma(0)=p$ and $\gamma(L+1)=q$.
--
--   This identity expresses a ReLU network with zero biases as a polynomial in its weights whose coefficients are the activation indicators. All the moment computations of Lecture 5 start from it.
--
--   **Formalization Note** The statement is deterministic, with no probability involved. The notes index weights along a path as $W^{(\ell)}_{\gamma(\ell-1)\gamma(\ell)}$; here the row/column orientation of the network recursion is used.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 40, eq. (123) (Section 5.3, Definition 2 and the exercise following it).

import Mathlib
import Definitions.Def_LesHouchesWidth_ReLUNet

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem output_eq_sum_over_paths {n : ℕ → ℕ} {L : ℕ} (ω : Weights n L)
    (x : Fin (n 0) → ℝ) (q : Fin (n (L + 1))) :
    output ω x q =
      ∑ p : Fin (n 0), x p *
        ∑ γ ∈ pathsFromTo n L p q, pathWeight ω γ * pathActivation ω x γ := by sorry

end LesHouchesWidth
