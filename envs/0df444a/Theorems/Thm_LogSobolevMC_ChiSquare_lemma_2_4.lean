-- Prove2me | Theorems.Thm_LogSobolevMC_ChiSquare_lemma_2_4
-- name    : LogSobolevMC.ChiSquare.lemma_2_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:02:08.472625+00:00
-- url     : https://prove2.me/theorems/891b1fbf-928c-42a1-9516-f47a260c056b
-- title:
--   Lemma 2.4 — spectral-gap decay in ℓ²
-- statement:
--   Let $K$ be a finite-state Markov chain with positive stationary distribution $\pi$, and let $\lambda$ be its variational spectral gap. For every real function $f$ and $t\ge0$,
--
--   $$
--   \|(H_t-E_\pi)f\|_2^2\le e^{-2t\lambda}\operatorname{Var}_\pi(f).
--   $$
--
--   The result controls how quickly the continuous-time semigroup removes the centered part of a function. It does not require reversibility.
--
--   **Formalization Note** Time is restricted to $t\ge0$, the domain of the Markov semigroup in this application.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 706, Lemma 2.4, https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.ChiSquare

theorem lemma_2_4 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (t : ℝ) (ht : 0 ≤ t) (f : V → ℝ) :
    lpNorm π 2 (fun x => heatOp K t f x - MarkovMixing.distExp π f) ^ 2 ≤
      Real.exp (-2 * t * gap K π) * MarkovMixing.distVar π f := by sorry

end LogSobolevMC.ChiSquare
