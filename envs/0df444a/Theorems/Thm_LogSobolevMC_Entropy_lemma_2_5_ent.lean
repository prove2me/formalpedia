-- Prove2me | Theorems.Thm_LogSobolevMC_Entropy_lemma_2_5_ent
-- name    : LogSobolevMC.Entropy.lemma_2_5_ent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:40.98568+00:00
-- url     : https://prove2.me/theorems/6a8ed9ed-7f28-4104-824f-6d858bb52065
-- title:
--   Lemma 2.5 (second part), p. 707 — ∂_t Ent_π(H_t f)|_{t=0} = −ℰ(f, log f)
-- statement:
--   Let $K$ be a Markov kernel on a finite set $\mathcal X$ with invariant probability $\pi$, $\pi(x)>0$ for all $x$, let $H_t=e^{-t(I-K)}$ be the associated semigroup and $\mathcal E(f,g)=\langle (I-K)f,g\rangle_\pi$ the Dirichlet form. For a function $f$ with $f(x)>0$ for all $x$, write $\mathrm{Ent}_\pi(g)=\sum_x g(x)\log g(x)\,\pi(x)$. Then
--
--   $$\partial_t\,\mathrm{Ent}_\pi(H_tf)\big|_{t=0}=-\mathcal E(f,\log f).$$
--
--   This is the entropy counterpart of the formula $\partial_t\|H_tf\|_p^p|_{t=0}=-p\,\mathcal E(f,f^{p-1})$; applied to the adjoint chain it gives the time derivative of the entropy along the semigroup, which drives the proof of Theorem 3.6.
--
--   **Formalization Note** The derivative is a two-sided derivative at $t=0$ (the series defining $H_t$ makes sense for all real $t$). The paper states the lemma for nonnegative $f$; the Lean statement asks $f>0$, because $\log f$ is $-\infty$ at a zero of $f$ on the page but Lean's `Real.log 0 = 0`. The normalisation $E_\pi f=1$ under which the paper calls $\sum f\log f\,\pi$ an entropy is not assumed: invariance of $\pi$ makes the formula hold without it.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 707, Lemma 2.5 (second display)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting

namespace LogSobolevMC.Entropy

theorem lemma_2_5_ent {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hf : ∀ x, 0 < f x) :
    HasDerivAt (fun t : ℝ => entF π (LogSobolevMC.ChiSquare.heatOp K t f))
      (-LogSobolevMC.ChiSquare.dirichlet K π f (fun x => Real.log (f x))) 0 := by sorry

end LogSobolevMC.Entropy
