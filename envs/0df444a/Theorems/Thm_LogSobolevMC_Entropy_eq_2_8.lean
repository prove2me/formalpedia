-- Prove2me | Theorems.Thm_LogSobolevMC_Entropy_eq_2_8
-- name    : LogSobolevMC.Entropy.eq_2_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:08:09.902022+00:00
-- url     : https://prove2.me/theorems/aedfc596-566e-4544-92df-238ceb239a22
-- title:
--   (2.8), p. 710 — 2‖μ − π‖²_TV ≤ Ent_π(μ) ≤ ‖μ − π‖_TV + ½‖(μ/π) − 1‖²_{π,2}
-- statement:
--   Let $\pi$ and $\mu$ be probability measures on a finite set $\mathcal X$, with $\pi(x)>0$ for all $x$. Write $\|\mu-\pi\|_{TV}=\sup_{A\subset\mathcal X}|\mu(A)-\pi(A)|$ for the total variation distance, $\mathrm{Ent}_\pi(\mu)=\sum_x\mu(x)\log\frac{\mu(x)}{\pi(x)}$ for the relative entropy, and $\|g\|_{\pi,2}=\big(\sum_x|g(x)|^2\pi(x)\big)^{1/2}$. Then
--
--   $$2\|\mu-\pi\|_{TV}^2\ \le\ \mathrm{Ent}_\pi(\mu)\ \le\ \|\mu-\pi\|_{TV}+\tfrac12\Big\|\frac{\mu}{\pi}-1\Big\|_{\pi,2}^2.$$
--
--   The lower bound is Pinsker's inequality; it converts entropy bounds, such as those given by the log-Sobolev constant, into total variation bounds. The upper bound compares entropy with the chi-square distance.
--
--   **Formalization Note** No Markov chain is involved; $\pi$ only needs to be a positive probability. Terms with $\mu(x)=0$ in the entropy are $0$ (Lean's `Real.log 0 = 0`). The total variation distance is the published `MarkovMixing.tvDist`, a supremum over the finitely many subsets.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 710, §2.4, (2.8)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_mixing
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Entropy

theorem eq_2_8 {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : MarkovMixing.IsDist π) (hπpos : ∀ x, 0 < π x)
    (μ : V → ℝ) (hμ : MarkovMixing.IsDist μ) :
    2 * MarkovMixing.tvDist μ π ^ 2 ≤ relEnt π μ ∧
      relEnt π μ ≤
        MarkovMixing.tvDist μ π + 1 / 2 * LogSobolevMC.ChiSquare.lpNorm π 2 (fun x => μ x / π x - 1) ^ 2 := by sorry

end LogSobolevMC.Entropy
