-- Prove2me | Theorems.Thm_OAI_Erdos3_smooth_window_weighted_sampled_error
-- name    : OAI.Erdos3.smooth_window_weighted_sampled_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:30:40.852915+00:00
-- url     : https://prove2.me/theorems/1c1dd168-341e-44a6-81d2-a14bd404f5b7
-- title:
--   Weighted window averages of a sampled error are controlled by smooth pair correlations
-- statement:
--   Let $K,I,P$ be finite types. Let $a,S\colon\mathrm{Option}\,K\times I\to\mathbb R$ with $S>0$ everywhere, and with $0<$ `shiftedSmoothProductMass a S` $=\sum_{z}\prod_{c}\phi\big((z_c-a_c)/S_c\big)$ (sum over integer arrays $z\colon\mathrm{Option}\,K\times I\to\mathbb Z$, $\phi=$ `smoothProbabilityProfile`, OpenAI's fixed smooth compactly supported profile $\mathbb R\to[0,1]$). Assume $8\,\ell\le S_c$ for every $c$, where $\ell=$ `probabilityProfileLipschitz` is a Lipschitz constant of $\phi$. Let $W$ be a finite set of integer arrays with $|z_c-a_c|\le S_c/2$ for all $z\in W$ and all $c$. Let $q$ be `FiniteProbabilityWeights` on $P$ and $t\colon P\to(K\to\mathbb Z)$; for $\tau\colon K\to\mathbb Z$ write $s_\tau(z)\in\mathbb Z^I$ for `smoothAffineSample τ z`, $s_\tau(z)_i=z(\mathrm{none},i)+\sum_{k\in K}\tau_k\,z(\mathrm{some}\ k,i)$. Let $T\subseteq\mathbb Z^I$ be finite and $e\colon\mathbb Z^I\to\mathbb R$ vanish off $T$, and let $E,\varepsilon,\beta$ be reals with $E\ge0$, $\varepsilon\ge0$ and $\sum_{y\in T}e(y)^2\le E\,|T|$. Let $\mathrm{Bad}$ be a predicate on $P\times P$ whose probability under the product weights $q\times q$ is at most $\beta$, and assume that for every $u=(u_1,u_2)$ not in $\mathrm{Bad}$, $\big|\mathbb E_{z}\,e(s_{t(u_1)}(z))\,e(s_{t(u_2)}(z))\big|\le\varepsilon$, the mean taken under `smoothSourceFiniteWeights a S hS hZ` (the probability weights on the finite box of integer arrays with $\lceil a_c-S_c\rceil\le z_c\le\lfloor a_c+S_c\rfloor$, with weight proportional to $\prod_c\phi((z_c-a_c)/S_c)$). Then for every $v$ from integer arrays to $[0,1]$,
--   $$\Big|\mathbb E_{z\in W}\,v(z)\sum_{p\in P}q(p)\,e(s_{t(p)}(z))\Big|\le\frac{3^{|\mathrm{Option}\,K\times I|}\prod_cS_c}{|W|}\sqrt{\Big(\prod_{i\in I}\frac2{S(\mathrm{none},i)}\Big)E\,|T|\,\beta+\varepsilon},$$
--   where $\mathbb E_{z\in W}$ is the uniform average over $W$ (Mathlib's `Finset.expect`) and $\prod_c S_c$ runs over $\mathrm{Option}\,K\times I$.
--
--   Lean: `OAI.Erdos3.smooth_window_weighted_sampled_error` in `lean/OAI/Combinatorics/Progressions/Estimates/WeightedSmoothSampledError.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/WeightedSmoothSampledError.lean#L181

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smooth_window_weighted_sampled_error {K I P : Type*}
    [Fintype K] [Fintype I] [Fintype P]
    (a S : Option K × I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ S i)
    (W : Finset (Option K × I → ℤ))
    (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - a i| ≤ S i / 2)
    (q : FiniteProbabilityWeights P) (t : P → K → ℤ)
    (T : Finset (I → ℤ)) (e : (I → ℤ) → ℝ) (he : ∀ y ∉ T, e y = 0)
    {E epsilon beta : ℝ} (hE : 0 ≤ E) (hepsilon : 0 ≤ epsilon)
    (henergy : (∑ y ∈ T, e y ^ 2) ≤ E * T.card)
    (Bad : P × P → Prop) (hmass : (q.prod q).eventProbability Bad ≤ beta)
    (hgood : ∀ u, ¬ Bad u → |(smoothSourceFiniteWeights a S hS hZ).mean
      (fun z => e (smoothAffineSample (t u.1) z.val) * e (smoothAffineSample (t u.2) z.val))| ≤ epsilon)
    (v : (Option K × I → ℤ) → ℝ) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) :
    |𝔼 z ∈ W, v z * q.mean (fun u => e (smoothAffineSample (t u) z))| ≤
      ((3 : ℝ) ^ Fintype.card (Option K × I) * (∏ i, S i) / W.card) *
        Real.sqrt (((∏ i, 2 / S (none, i)) * (E * T.card)) * beta + epsilon) := by
  sorry

end Erdos3
end
end OAI
