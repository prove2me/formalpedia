-- Prove2me | Theorems.Thm_HaagerupReduction_Dyadic_lemma_2_2
-- name    : HaagerupReduction.Dyadic.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:18.078665+00:00
-- url     : https://prove2.me/theorems/a4ffd074-d58d-41e5-b6be-41e56563682c
-- title:
--   Lemma 2.2, p. 7 — φ̂(f(λ(t))) = ∫_𝕋 f dm for t ∈ G ∖ {0}: λ(t) is Haar-distributed under φ̂
-- statement:
--   Let $(M,\varphi)$, $G$, $\lambda$ and the dual state $\hat\varphi(y) = \langle y\hat\xi,\hat\xi\rangle$ on $\ell^2(G,H)$ be as in the model, and let $dm$ be normalized Haar measure on the unit circle $\mathbb T$. For every $t\in G\setminus\{0\}$ and every function $f$ continuous on $\mathbb T$,
--   $$\hat\varphi\big(f(\lambda(t))\big) = \int_{\mathbb T} f(z)\,dm(z) = \frac{1}{2\pi}\int_0^{2\pi} f(e^{i\theta})\,d\theta .$$
--
--   In other words, the distribution of the unitary $\lambda(t)$ with respect to $\hat\varphi$ is $dm$. This is used for the uniqueness of $b_n$ in Lemma 2.3 and for the $L_2$ estimate of $b_n$ in Lemma 2.6.
--
--   **Formalization Note.** The paper states the identity for $f\in L_\infty(\mathbb T)$ with the Borel functional calculus; Lean has only the continuous functional calculus `cfc`, so $f$ is continuous on $\mathbb T$ (it may be any function $\mathbb C\to\mathbb C$ continuous on the circle). The continuous case already determines the distribution measure, which is the lemma's second sentence. `cfc f u` is a junk value only when $u$ is not normal or $f$ is not continuous on its spectrum; $\lambda(t)$ is unitary with spectrum in $\mathbb T$, so neither happens.
-- source:
--   Haagerup, Junge & Xu, A reduction method for noncommutative Lp-spaces and applications, arXiv:0806.3635v2, p. 7, Lemma 2.2 (display (2.1))

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HaagerupReduction_Dyadic_Model

namespace HaagerupReduction.Dyadic

universe u

open OAI.BoundedRecovery
open Filter Topology

/-- Lemma 2.2 (continuous `f`): `φ̂(f(λ(t))) = ∫_𝕋 f dm` for `t ∈ G ∖ {0}`. -/
theorem lemma_2_2 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : StandardModularData H) (t : dyadic) (ht : t ≠ 0)
    (f : ℂ → ℂ) (hf : ContinuousOn f (Metric.sphere (0 : ℂ) 1)) :
    phiHat S (cfc f (lam H t)) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), f (Complex.exp ((θ : ℂ) * Complex.I)) := by sorry

end HaagerupReduction.Dyadic
