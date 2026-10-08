-- Prove2me | Theorems.Thm_LogSobolevMC_LowerBound_eq_3_7
-- name    : LogSobolevMC.LowerBound.eq_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:08:03.607159+00:00
-- url     : https://prove2.me/theorems/df35fa16-1d7e-4b0a-9570-88f0045800a3
-- title:
--   Equation (3.7), p. 727 — Rothaus's centering inequality
-- statement:
--   Let $\pi$ be a strictly positive probability distribution on a finite state space, and write $Ef=\sum_x f(x)\pi(x)$. For every real function $f$,
--
--   $$
--   \mathcal L(f)\le\mathcal L(f-Ef)+2\|f-Ef\|_2^2.
--   $$
--
--   This inequality controls the entropy of a function by that of its centered version and its variance. The paper cites earlier proofs rather than proving it here.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 727, §3.4, (3.7); https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_LowerBound_Setting

namespace LogSobolevMC.LowerBound

theorem eq_3_7 {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : MarkovMixing.IsDist π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) :
    LogSobolevMC.ChiSquare.entL π f ≤
      LogSobolevMC.ChiSquare.entL π (fun x => f x - MarkovMixing.distExp π f) +
        2 * LogSobolevMC.ChiSquare.lpNorm π 2 (fun x => f x - MarkovMixing.distExp π f) ^ 2 := by sorry

end LogSobolevMC.LowerBound
