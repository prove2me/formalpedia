-- Prove2me | Theorems.Thm_LogSobolevMC_Entropy_lemma_2_7
-- name    : LogSobolevMC.Entropy.lemma_2_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:28.696261+00:00
-- url     : https://prove2.me/theorems/656585fa-7f6d-462d-9098-0c0fba762de1
-- title:
--   Lemma 2.7, p. 708 — ℰ(log f, f) ≥ 2ℰ(√f, √f), and ≥ 4ℰ(√f, √f) for reversible chains
-- statement:
--   Let $K$ be a Markov kernel on a finite set $\mathcal X$ with invariant probability $\pi$, $\pi(x)>0$ for all $x$, and let $\mathcal E(f,g)=\langle (I-K)f,g\rangle_\pi=\sum_x\big(f(x)-Kf(x)\big)g(x)\pi(x)$. For every function $f$ with $f(x)>0$ for all $x$:
--
--   1. $$\mathcal E(\log f,f)\ \ge\ 2\,\mathcal E(\sqrt f,\sqrt f);$$
--   2. if $(K,\pi)$ is reversible, i.e. $\pi(x)K(x,y)=\pi(y)K(y,x)$ for all $x,y$, then
--   $$\mathcal E(\log f,f)\ \ge\ 4\,\mathcal E(\sqrt f,\sqrt f).$$
--
--   Combined with the log-Sobolev inequality applied to $\sqrt f$, these inequalities bound the entropy dissipation from below by $2\alpha$ (resp. $4\alpha$) times the entropy, which yields the two decay rates of Theorem 3.6.
--
--   **Formalization Note** The order of arguments in $\mathcal E(\log f,f)$ is the paper's; $\mathcal E$ is not symmetric for nonreversible chains. The paper states the lemma for $f\ge0$ with $\log 0=-\infty$; with Lean's `Real.log 0 = 0` that version fails, so the Lean statement asks $f>0$.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 708, Lemma 2.7

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Entropy

theorem lemma_2_7 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hf : ∀ x, 0 < f x) :
    2 * LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.sqrt (f x)) (fun x => Real.sqrt (f x)) ≤
        LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.log (f x)) f ∧
      (MarkovMixing.DetailedBalance K π →
        4 * LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.sqrt (f x)) (fun x => Real.sqrt (f x)) ≤
          LogSobolevMC.ChiSquare.dirichlet K π (fun x => Real.log (f x)) f) := by sorry

end LogSobolevMC.Entropy
