-- Prove2me | Theorems.Thm_NondomArb_Superhedge_lemma_A_2
-- name    : NondomArb.Superhedge.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:13.776984+00:00
-- url     : https://prove2.me/theorems/f5f50b8f-af37-447e-924a-e354791d988e
-- title:
--   Lemma A.2 — if x + H • S_T + hg ≥ f Q-a.s. and S − S₀ is a local Q-martingale with E_Q[gⁱ] = 0, then E_Q[f] ≤ x
-- statement:
--   Let $(\Omega,\mathcal F,Q)$ be a probability space with a filtration $(\mathcal F_t)_{t=0,\dots,T}$, let $S$ be an adapted $\mathbb R^d$-valued process, and let predictable strategies $H$ and the wealth $H\bullet S_T$ be as in (1.2).
--
--   **Lemma.** Let $f$ (with values in $[-\infty,\infty]$) and $g=(g^1,\dots,g^e)$ be $\mathcal F$-measurable, and suppose $E_Q[g^i]=0$ for all $i$ and $S-S_0$ is a local $Q$-martingale. If there exist $x\in\mathbb R$ and $(H,h)\in\mathcal H\times\mathbb R^e$ such that
--   $$x+H\bullet S_T+hg\ge f\qquad Q\text{-a.s.},$$
--   then $E_Q[f]\le x$.
--
--   This is the "easy" inequality of superhedging duality: the price of any superhedge dominates the expectation under any consistent martingale measure.
--
--   **Formalization Note** $E_Q[f]$ and $E_Q[g^i]$ are extended expectations (1.1) in `EReal`. A local martingale is defined with $\mathbb N$-valued stopping times $\tau_n$, nondecreasing in $n$ and tending to $\infty$ $Q$-a.s., whose stopped processes are martingales on $\{0,\dots,T\}$.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 35, Appendix, Lemma A.2

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_General
open MeasureTheory Filter Topology NondomArb.Superhedge.General

namespace NondomArb.Superhedge

/-- **Lemma A.2** (p. 35). On a filtered probability space, let `S` be adapted, `f` and
`g = (g¹, …, gᵉ)` be measurable, `E_Q[gⁱ] = 0` for all `i`, and `S − S_0` a local `Q`-martingale. If
`x + H • S_T + hg ≥ f` `Q`-a.s. for some `x ∈ ℝ` and `(H, h) ∈ ℋ × ℝ^e`, then `E_Q[f] ≤ x`. -/
theorem lemma_A_2 {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m)
    (Q : Measure Ω) [IsProbabilityMeasure Q] {T d e : ℕ}
    (S : ℕ → Ω → (Fin d → ℝ)) (hS : ∀ t ≤ T, Measurable[ℱ t] (S t))
    (f : Ω → EReal) (hf : Measurable f) (g : Ω → (Fin e → ℝ)) (hg : Measurable g)
    (hgQ : ∀ i : Fin e, extExp Q (fun ω => ((g ω i : ℝ) : EReal)) = 0)
    (hloc : IsLocalMartingaleOn Q ℱ T (fun t ω => S t ω - S 0 ω))
    (x : ℝ) (H : ℕ → Ω → (Fin d → ℝ)) (hH : IsPredictable ℱ T H) (h : Fin e → ℝ)
    (hsup : ∀ᵐ ω ∂Q, f ω ≤ ((x + wealth T S H ω + h ⬝ᵥ g ω : ℝ) : EReal)) :
    extExp Q f ≤ x := by sorry

end NondomArb.Superhedge
