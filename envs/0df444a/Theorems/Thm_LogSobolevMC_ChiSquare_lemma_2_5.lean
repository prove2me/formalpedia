-- Prove2me | Theorems.Thm_LogSobolevMC_ChiSquare_lemma_2_5
-- name    : LogSobolevMC.ChiSquare.lemma_2_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:02:05.032977+00:00
-- url     : https://prove2.me/theorems/20eccca9-2e13-4b66-ad51-32cf6f72fa89
-- title:
--   Lemma 2.5 — derivative of the p-th moment at zero
-- statement:
--   Let $K$ be a finite-state Markov chain with positive stationary distribution $\pi$. For $p\ge1$ and every nonnegative function $f$,
--
--   $$
--   \left.\frac{d}{dt}\|H_t f\|_p^p\right|_{t=0+}=-p\,\mathcal E(f,f^{p-1}).
--   $$
--
--   This identity relates the change in a weighted moment under the heat semigroup to the bilinear Dirichlet form.
--
--   **Formalization Note** The derivative is from the right because $H_t$ is used for nonnegative time and $f$ may vanish.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 707, Lemma 2.5, first identity, https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.ChiSquare

theorem lemma_2_5 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x)
    (p : ℝ) (hp : 1 ≤ p) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) :
    HasDerivWithinAt (fun t : ℝ => ∑ x, |heatOp K t f x| ^ p * π x)
      (-p * dirichlet K π f (fun x => f x ^ (p - 1))) (Set.Ici 0) 0 := by sorry

end LogSobolevMC.ChiSquare
