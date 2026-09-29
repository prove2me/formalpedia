-- Prove2me | Theorems.Thm_LesHouchesWidth_output_law_eq_dropout_law
-- name    : LesHouchesWidth.output_law_eq_dropout_law
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T22:01:33.902107+00:00
-- url     : https://prove2.me/theorems/54dae77a-c612-4072-911b-6905799ee77e
-- title:
--   Proposition 5.2: exact matrix model (ReLU network = deep linear network with dropout in law)
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$ that has a density with respect to Lebesgue measure, is symmetric about $0$, and has variance $\int t^2d\mu=1$. Let $L\ge1$ and $n_0,\dots,n_{L+1}\ge1$, and let the weights be $W^{(\ell)}_{ij}=(2/n_{\ell-1})^{1/2}\widehat W^{(\ell)}_{ij}$ with $\widehat W^{(\ell)}_{ij}$ i.i.d. $\sim\mu$ and zero biases. Then for every fixed input $x\neq0$, the ReLU network output $z^{(L+1)}(x)$ satisfies
--   $$z^{(L+1)}(x)\ \overset{d}{=}\ W^{(L+1)}D^{(L)}W^{(L)}\cdots D^{(1)}W^{(1)}x,$$
--   where $D^{(\ell)}=\mathrm{diag}(\xi^{(\ell)}_1,\dots,\xi^{(\ell)}_{n_\ell})$ with $\xi^{(\ell)}_i$ i.i.d. Bernoulli$(1/2)$, independent of the weights.
--
--   This reduces the analysis of random ReLU networks at one input to that of products of random matrices with dropout.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 39, Proposition 5.2 (Section 5.3, with the standing assumptions on $\mu$ stated just before it).

import Mathlib
import Definitions.Def_LesHouchesWidth_ReLUNet

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem output_law_eq_dropout_law (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_ac : μ ≪ volume) (hμ_symm : μ.map (fun t : ℝ => -t) = μ)
    (hμ_var : ∫ t, t ^ 2 ∂μ = 1)
    (L : ℕ) (hL : 1 ≤ L) (n : ℕ → ℕ) (hn : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ)
    (x : Fin (n 0) → ℝ) (hx : x ≠ 0) :
    (weightLaw n L μ).map (fun ω => output ω x) =
      ((weightLaw n L μ).prod (maskLaw n L)).map (fun ωξ => dropoutOutput ωξ.1 ωξ.2 x) := by sorry

end LesHouchesWidth
