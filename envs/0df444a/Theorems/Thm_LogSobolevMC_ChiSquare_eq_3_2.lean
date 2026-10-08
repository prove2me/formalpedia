-- Prove2me | Theorems.Thm_LogSobolevMC_ChiSquare_eq_3_2
-- name    : LogSobolevMC.ChiSquare.eq_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:02:06.394976+00:00
-- url     : https://prove2.me/theorems/ec7e4fe7-bb44-49d7-9c85-486232a30b06
-- title:
--   Equation (3.2) — derivative of a varying-exponent heat norm
-- statement:
--   Let $K$ be a finite-state Markov chain with positive stationary distribution $\pi$. Let $f$ be strictly positive, $t\ge0$, and let $p(s)$ be differentiable at $t$ with $p(t)\ge1$. Set $F(s)=\|H_s f\|_{p(s)}$. Then
--
--   $$
--   F'(t)=F(t)^{1-p(t)}\left[\frac{p'(t)}{p(t)^2}\mathcal L_{p(t)}(H_t f)-\mathcal E\bigl(H_t f,(H_t f)^{p(t)-1}\bigr)\right].
--   $$
--
--   This derivative identity is the displayed calculation used to relate heat-flow norms and entropy in Theorem 3.5.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 721, display (3.2), https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.ChiSquare

theorem eq_3_2 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (f : V → ℝ) (hf : ∀ x, 0 < f x)
    (p : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (hp : 1 ≤ p t)
    (p' : ℝ) (hp' : HasDerivAt p p' t) :
    let F := fun s : ℝ => lpNorm π (p s) (heatOp K s f)
    HasDerivAt F
      (F t ^ (-(p t) + 1) *
        (p' / (p t) ^ 2 * entLp π (p t) (heatOp K t f) -
          dirichlet K π (heatOp K t f)
            (fun x => heatOp K t f x ^ (p t - 1)))) t := by sorry

end LogSobolevMC.ChiSquare
