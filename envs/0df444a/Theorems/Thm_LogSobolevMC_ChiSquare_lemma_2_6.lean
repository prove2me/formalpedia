-- Prove2me | Theorems.Thm_LogSobolevMC_ChiSquare_lemma_2_6
-- name    : LogSobolevMC.ChiSquare.lemma_2_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:02:21.478325+00:00
-- url     : https://prove2.me/theorems/76e7ec9a-6465-417d-935e-ca3bf263baf6
-- title:
--   Lemma 2.6 — Dirichlet-form power inequalities
-- statement:
--   Let $K$ be a finite-state Markov chain with positive stationary distribution $\pi$, and let $f\ge0$. If $p\ge2$, then
--
--   $$
--   \mathcal E(f,f^{p-1})\ge\frac2p\mathcal E(f^{p/2},f^{p/2}).
--   $$
--
--   If the chain is reversible, then for every $1<p<\infty$ the stronger inequality holds:
--
--   $$
--   \mathcal E(f,f^{p-1})\ge\frac{4(p-1)}{p^2}\mathcal E(f^{p/2},f^{p/2}).
--   $$
--
--   These bounds connect power transforms of a function to the bilinear Dirichlet form and underlie the different hypercontractive time scales.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 707, Lemma 2.6, https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.ChiSquare

theorem lemma_2_6 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∀ p : ℝ, 2 ≤ p →
      2 / p * dirichlet K π (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2)) ≤
        dirichlet K π f (fun x => f x ^ (p - 1))) ∧
    (MarkovMixing.DetailedBalance K π → ∀ p : ℝ, 1 < p →
      4 * (p - 1) / p ^ 2 *
          dirichlet K π (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2)) ≤
        dirichlet K π f (fun x => f x ^ (p - 1))) := by sorry

end LogSobolevMC.ChiSquare
