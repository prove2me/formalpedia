-- Prove2me | Theorems.Thm_GevreyGibbsSep_corollary_A_2
-- name    : GevreyGibbsSep.corollary_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:41:47.405885+00:00
-- url     : https://prove2.me/theorems/345ede2e-eab6-4a34-a89c-90b333197b90
-- title:
--   Corollary A.2 — $p\in G^s(\alpha,\rho/(d+\xi+1))$ and $\sqrt p\in G^s(\alpha^{1/2},\rho/(d+\xi/2+1))$
-- statement:
--   Let $p=e^{-\beta E}/Z\in\mathscr W^s(\alpha,\xi,\rho)$ with $s\ge1$. Then
--   $$p\in G^s\Big(\alpha,\ \frac{\rho}{d+\xi+1}\Big)\qquad\text{and}\qquad \sqrt p\in G^s\Big(\alpha^{1/2},\ \frac{\rho}{d+\xi/2+1}\Big).$$
--
--   Membership in the potential class makes the density and its square root Gevrey functions, which the quantum sampler's discretization requires.
--
--   Differences from the source:
--   - encoding: instances are Gibbs states $p=e^{-\beta E}/Z$ → instances are scaled potentials $V=\beta E$ with Gibbs state $e^{-V}/Z_V$; reason: two potentials with the same Gibbs state give the same oracle answers and the same target
--   - encoding: $s\ge1$, $p\in\mathscr W^s(\alpha,\xi,\rho)$ (Definition 2: $\alpha\ge1$, $\xi,\rho>0$), dimension $d$ → hypotheses $s\ge1$, $\alpha\ge1$, $\xi,\rho>0$, $d\ge1$; reason: the ranges of Definition 2 and the paper's standing dimension
--   - encoding: $[\beta E]_{s,\rho}\le\xi$ with the supremum over $x\in[0,2\pi)^d$, and $\beta\Delta\le\log\alpha$ → $|\partial^aV(x)|\,\rho^{\|a\|_1}\le\xi\,(a!)^s$ for every $a\ne0$ and every $x\in\mathbb R^d$, and $V(x)-V(y)\le\log\alpha$ for all $x,y$; reason: equivalent for a continuous $2\pi$-periodic $V$: its values and derivatives on $\mathbb R^d$ are those on the period cell, where the maximum and minimum are attained
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Corollary A.2, Eq. (A28), p.23

import Mathlib
import Definitions.Def_GevreyGibbsSep_InGevrey
import Definitions.Def_GevreyGibbsSep_partitionFn
import Definitions.Def_GevreyGibbsSep_GibbsClass

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Corollary A.2 (density regularity from class parameters), arXiv:2608.24527 (sha256
d4fd40eb…), Eq. (A28), p.23. If `p = e^{−βE}/Z ∈ W^s(α, ξ, ρ)` with `s ≥ 1`, then
`p ∈ G^s(α, ρ/(d + ξ + 1))` and `√p ∈ G^s(α^{1/2}, ρ/(d + ξ/2 + 1))`.

**Formalization Note** `V = βE` is the class member; `p = e^{−V}/Z_V` on `ℝ^d`. `d ≥ 1` and the
ranges `α ≥ 1`, `ξ, ρ > 0` of Definition 2 are hypotheses. -/
theorem corollary_A_2 {d : ℕ} (hd : 0 < d) (s α ξ ρ : ℝ) (hs : 1 ≤ s) (hα : 1 ≤ α)
    (hξ : 0 < ξ) (hρ : 0 < ρ) (V : (Fin d → ℝ) → ℝ) (hV : V ∈ GibbsClass d s α ξ ρ) :
    InGevrey s α (ρ / (d + ξ + 1)) (fun x => Real.exp (- V x) / partitionFn V) ∧
    InGevrey s (Real.sqrt α) (ρ / (d + ξ / 2 + 1))
      (fun x => Real.sqrt (Real.exp (- V x) / partitionFn V)) := by sorry

end GevreyGibbsSep
