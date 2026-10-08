-- Prove2me | Theorems.Thm_LogSobolevMC_TwoPoint_alpha_dichotomy
-- name    : LogSobolevMC.TwoPoint.alpha_dichotomy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:00:57.848273+00:00
-- url     : https://prove2.me/theorems/3dd31cec-3778-4337-948e-35f30d7bb0a5
-- title:
--   Proof of Theorem A.1, p. 746 — either α = λ/2 or (A.2) has a nonconstant nonnegative minimizer
-- statement:
--   Let $K$ be a Markov kernel on a finite set $\mathcal X$ with invariant probability $\pi>0$, log-Sobolev constant $\alpha$ and spectral gap $\lambda$. Then at least one of the following holds:
--
--   1. $\alpha=\lambda/2$;
--   2. there is a nonnegative function $f_0$ on $\mathcal X$ with $\mathcal L(f_0)\ne0$ (so $f_0$ is not constant) that attains the infimum (A.2): $$\mathcal E(f_0,f_0)=\alpha\,\mathcal L(f_0).$$
--
--   The paper notes that this reasoning is valid for any finite Markov chain. It reduces the computation of $\alpha$ to the study of minimizers whenever $\alpha<\lambda/2$.
--
--   **Formalization Note** "Nonconstant" is expressed by $\mathcal L(f_0)\neq0$ (which forces $f_0$ to be nonconstant), and "minimizes (A.2)" by the equality $\mathcal E(f_0,f_0)=\alpha\mathcal L(f_0)$. No irreducibility is assumed; on a one-point space both $\alpha$ and $\lambda$ are infima over the empty set and the first alternative holds.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 746, proof of Theorem A.1, paragraph after (A.2) and the sentence after the display

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_TwoPoint_Setting

namespace LogSobolevMC.TwoPoint

open MarkovMixing

/-- Proof of Theorem A.1, p. 746: for any finite Markov chain, either `α = λ/2` or the
infimum (A.2) is attained at a nonconstant nonnegative function `f₀`. -/
theorem alpha_dichotomy {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) :
    2 * LogSobolevMC.ChiSquare.logSobolev K π = LogSobolevMC.ChiSquare.gap K π ∨
      ∃ f₀ : V → ℝ, (∀ x, 0 ≤ f₀ x) ∧ LogSobolevMC.ChiSquare.entL π f₀ ≠ 0 ∧
        LogSobolevMC.ChiSquare.dirichlet K π f₀ f₀ = LogSobolevMC.ChiSquare.logSobolev K π * LogSobolevMC.ChiSquare.entL π f₀ := by sorry

end LogSobolevMC.TwoPoint
