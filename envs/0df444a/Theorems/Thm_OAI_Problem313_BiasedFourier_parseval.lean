-- Prove2me | Theorems.Thm_OAI_Problem313_BiasedFourier_parseval
-- name    : OAI.Problem313.BiasedFourier.parseval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:47:29.633805+00:00
-- url     : https://prove2.me/theorems/104381c2-0c55-4dc1-9fe1-a7ac8efb2fa2
-- title:
--   Parseval's identity for the $p$-biased Fourier basis
-- statement:
--   Let $\iota$ be a finite set and $0<p<1$. On $\{0,1\}^\iota$ let $w_p(x)=\prod_ip^{[x_i]}(1-p)^{1-[x_i]}$, $\chi_p(b)=([b]-p)/\sqrt{p(1-p)}$, $\chi_S(x)=\prod_{i\in S}\chi_p(x_i)$ and $\hat g(S)=\sum_xw_p(x)g(x)\chi_S(x)$. Then for every $g:\{0,1\}^\iota\to\mathbb{R}$,
--   $$
--   \sum_{S\subseteq\iota}\hat g(S)^2=\sum_xw_p(x)\,g(x)^2 .
--   $$
--
--   The squared Fourier coefficients of $g$ add up to its second moment. For a Boolean function this is the probability that it is true.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/FourierBasis.lean#L85-L107

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis

open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
universe u v
open scoped BigOperators
variable {ι : Type u} [Fintype ι]

theorem OAI.Problem313.BiasedFourier.parseval [DecidableEq ι] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) :
    (∑ S : Finset ι, coeff p g S ^ 2) = ∑ x, weight p x * (g x) ^ 2 := by sorry
