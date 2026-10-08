-- Prove2me | Theorems.Thm_LogSobolevMC_Entropy_entL_eq_relEnt
-- name    : LogSobolevMC.Entropy.entL_eq_relEnt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:36.706384+00:00
-- url     : https://prove2.me/theorems/db2fabd1-19dc-468e-abbf-458b13e3cf72
-- title:
--   §3.3, p. 722 — for f ≥ 0 with ‖f‖₂ = 1 and μ = f²π, ℒ(f) = Ent_π(μ)
-- statement:
--   Let $\pi$ be a probability on a finite set $\mathcal X$ with $\pi(x)>0$ for all $x$. Let $f\ge0$ be a function with $\|f\|_2=\big(\sum_x f(x)^2\pi(x)\big)^{1/2}=1$, and let $\mu=f^2\pi$, the probability measure $\mu(x)=f(x)^2\pi(x)$. Then
--
--   $$\mathcal L(f)=\sum_x |f(x)|^2\log\frac{|f(x)|^2}{\|f\|_2^2}\,\pi(x)=\mathrm{Ent}_\pi(\mu)=\sum_x\mu(x)\log\frac{\mu(x)}{\pi(x)}.$$
--
--   This identity is what makes the log-Sobolev constant $\alpha$ a rate for relative entropy: applied to $f=\sqrt{h}$ for a density $h$, it turns $\mathcal L(\sqrt h)\le\alpha^{-1}\mathcal E(\sqrt h,\sqrt h)$ into a bound on $\mathrm{Ent}_\pi(h\pi)$.
--
--   **Formalization Note** Terms with $f(x)=0$ are $0$ on both sides (Lean's `Real.log 0 = 0`, the convention $0\log0=0$).
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 722, §3.3, first paragraph

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Entropy

theorem entL_eq_relEnt {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : MarkovMixing.IsDist π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) (hf2 : LogSobolevMC.ChiSquare.lpNorm π 2 f = 1) :
    LogSobolevMC.ChiSquare.entL π f = relEnt π (fun x => f x ^ 2 * π x) := by sorry

end LogSobolevMC.Entropy
