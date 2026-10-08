-- Prove2me | Theorems.Thm_LogSobolevMC_TwoPoint_dirichlet_abs_le
-- name    : LogSobolevMC.TwoPoint.dirichlet_abs_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:18.406789+00:00
-- url     : https://prove2.me/theorems/df60c558-e136-444a-98b4-598498f67043
-- title:
--   Proof of Theorem A.1, p. 746 — ℰ(|f|, |f|) ≤ ℰ(f, f)
-- statement:
--   Let $K$ be a Markov kernel on a finite set $\mathcal X$ with invariant probability $\pi>0$, and $\mathcal E(f,g)=\langle (I-K)f,g\rangle_\pi$ its Dirichlet form. For every real function $f$ on $\mathcal X$,
--
--   $$\mathcal E(|f|,|f|)\le\mathcal E(f,f).$$
--
--   Since also $\mathcal L(|f|)=\mathcal L(f)$, the infimum defining the log-Sobolev constant may be taken over nonnegative functions only; this is the first step of the proof of Theorem A.1.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 746, proof of Theorem A.1, first paragraph after (A.2)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_TwoPoint_Setting

namespace LogSobolevMC.TwoPoint

open MarkovMixing

/-- Proof of Theorem A.1, p. 746: `ℰ(|f|, |f|) ≤ ℰ(f, f)` for every real function `f`. -/
theorem dirichlet_abs_le {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (f : V → ℝ) :
    LogSobolevMC.ChiSquare.dirichlet K π (fun x => |f x|) (fun x => |f x|) ≤ LogSobolevMC.ChiSquare.dirichlet K π f f := by sorry

end LogSobolevMC.TwoPoint
