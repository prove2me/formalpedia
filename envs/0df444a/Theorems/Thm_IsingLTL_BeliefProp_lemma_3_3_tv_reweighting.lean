-- Prove2me | Theorems.Thm_IsingLTL_BeliefProp_lemma_3_3_tv_reweighting
-- name    : IsingLTL.BeliefProp.lemma_3_3_tv_reweighting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:30.222696+00:00
-- url     : https://prove2.me/theorems/a3928a69-4c02-407b-a8a0-8fe247fcf7fa
-- title:
--   Total variation stability of reweighted distributions (Lemma 3.3)
-- statement:
--   Let $\mathcal X$ be a finite set, $f:\mathcal X\to[0,f_{\max}]$, and $\nu,\nu'$ distributions on $\mathcal X$ with $\nu(f>0)>0$ and $\nu'(f>0)>0$. Then
--   $$\sum_x\left|\frac{\nu(x)f(x)}{\langle\nu,f\rangle}-\frac{\nu'(x)f(x)}{\langle\nu',f\rangle}\right|\le\frac{3f_{\max}}{\max(\langle\nu,f\rangle,\langle\nu',f\rangle)}\,\|\nu-\nu'\|_{\mathrm{TV}}.$$
--   In particular, if $0<f_{\min}\le f(x)$ for all $x$, the right-hand side is at most $(3f_{\max}/f_{\min})\|\nu-\nu'\|_{\mathrm{TV}}$.
--
--   The lemma controls how a change of boundary distribution propagates through a bounded Boltzmann weight; it converts the root-magnetization bounds into total variation bounds on marginals (Theorem 4.2).
--
--   **Formalization Note** $\|\cdot\|_{\mathrm{TV}}=\tfrac12\ell^1$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 9, Lemma 3.3, eq. (3.3)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist

namespace IsingLTL.BeliefProp

/-- **Lemma 3.3** (Dembo–Montanari, arXiv:0804.4726v3, p. 9, eq. (3.3)). For any function
`f : 𝒳 → [0, f_max]` and distributions `ν, ν′` on the finite set `𝒳` with `ν(f > 0) > 0` and
`ν′(f > 0) > 0`,
`∑ₓ |ν(x)f(x)/⟨ν,f⟩ − ν′(x)f(x)/⟨ν′,f⟩| ≤ (3 f_max / max(⟨ν,f⟩, ⟨ν′,f⟩)) ‖ν − ν′‖_TV`.
In particular, if `0 < f_min ≤ f(x)` for all `x`, the right-hand side is at most
`(3 f_max / f_min) ‖ν − ν′‖_TV`.

Formalization Note: `‖·‖_TV = ½ ℓ¹` (`tvDist`); `ν(f > 0) > 0` is "some `x` has `ν(x) > 0` and
`f(x) > 0`". -/
theorem lemma_3_3_tv_reweighting {X : Type*} [Fintype X] (f : X → ℝ) (fmax : ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ fmax) (ν ν' : X → ℝ)
    (hν : IsDistribution ν) (hν' : IsDistribution ν')
    (hνf : ∃ x, 0 < ν x ∧ 0 < f x) (hν'f : ∃ x, 0 < ν' x ∧ 0 < f x) :
    ∑ x, |ν x * f x / IsingLTL.FreeEntropy.pairing ν f - ν' x * f x / IsingLTL.FreeEntropy.pairing ν' f| ≤
        3 * fmax / max (IsingLTL.FreeEntropy.pairing ν f) (IsingLTL.FreeEntropy.pairing ν' f) * tvDist ν ν' ∧
      ∀ fmin : ℝ, 0 < fmin → (∀ x, fmin ≤ f x) →
        3 * fmax / max (IsingLTL.FreeEntropy.pairing ν f) (IsingLTL.FreeEntropy.pairing ν' f) * tvDist ν ν' ≤
          3 * fmax / fmin * tvDist ν ν' := by sorry

end IsingLTL.BeliefProp
