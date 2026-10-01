-- Prove2me | Theorems.Thm_LesHouchesWidth_jacobianEntry_eq_sum_over_paths_ae
-- name    : LesHouchesWidth.jacobianEntry_eq_sum_over_paths_ae
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:08:42.659641+00:00
-- url     : https://prove2.me/theorems/5d4a74b5-9154-4d5a-aefb-cf04266d788c
-- title:
--   Section 5.4: the input–output Jacobian as a sum over paths (a.s.)
-- statement:
--   Under the standing assumptions of Section 5.3 ($\mu$ has a density, is symmetric, and has variance $1$; $L\ge1$; all widths $\ge1$), for every fixed input $x\neq0$ and all $p\le n_0$, $q\le n_{L+1}$, almost surely
--   $$\frac{\partial z^{(L+1)}_q}{\partial x_p}(x)=\sum_{\gamma\in\Gamma_{p,q}}\Big(\prod_{\ell=1}^{L+1}W^{(\ell)}_{\gamma(\ell)\gamma(\ell-1)}\Big)\Big(\prod_{\ell=1}^{L}\xi^{(\ell)}_{\gamma;x}\Big).$$
--
--   This identifies the Jacobian with a path sum that no longer involves the input except through the activation pattern.
--
--   **Formalization Note** The derivative is Mathlib's Fréchet derivative, which is $0$ where the network is not differentiable. The statement asserts the identity outside a null set of weights.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 40, Section 5.4, first exercise (first display).

import Mathlib
import Definitions.Def_LesHouchesWidth_ReLUNet

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem jacobianEntry_eq_sum_over_paths_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_ac : μ ≪ volume) (hμ_symm : μ.map (fun t : ℝ => -t) = μ)
    (hμ_var : ∫ t, t ^ 2 ∂μ = 1)
    (L : ℕ) (hL : 1 ≤ L) (n : ℕ → ℕ) (hn : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ)
    (x : Fin (n 0) → ℝ) (hx : x ≠ 0) (p : Fin (n 0)) (q : Fin (n (L + 1))) :
    ∀ᵐ ω ∂(weightLaw n L μ), jacobianEntry ω x p q =
      ∑ γ ∈ pathsFromTo n L p q, pathWeight ω γ * pathActivation ω x γ := by sorry

end LesHouchesWidth
