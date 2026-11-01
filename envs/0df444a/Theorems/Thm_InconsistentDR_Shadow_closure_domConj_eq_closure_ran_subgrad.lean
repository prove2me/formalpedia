-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_closure_domConj_eq_closure_ran_subgrad
-- name    : InconsistentDR.Shadow.closure_domConj_eq_closure_ran_subgrad
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T22:54:25.210584+00:00
-- url     : https://prove2.me/theorems/6024d4fe-65f6-4572-bdf4-734859d85eb7
-- title:
--   $\overline{\operatorname{dom}} f^* = \overline{\operatorname{ran}}\,\partial f$ for $f\in\Gamma_0(X)$ (proof of Theorem 6.9, p. 28)
-- statement:
--   Let $X$ be a real Hilbert space and $f \in \Gamma_0(X)$ (proper, convex, lower semicontinuous, with values in $]-\infty,+\infty]$). Let
--   $$f^*(u) = \sup_{x \in X}\big(\langle x, u\rangle - f(x)\big)$$
--   be its Fenchel conjugate and $\operatorname{dom} f^* = \{u : f^*(u) < +\infty\}$. Then
--   $$\overline{\operatorname{dom} f^*} = \overline{\operatorname{ran}\,\partial f}.$$
--
--   This is the identity used in the proof of Theorem 6.9 (p. 28) of the paper: "$0 \in \operatorname{dom} f^* + \operatorname{dom} g^* \subseteq \overline{\operatorname{dom}} f^* + \overline{\operatorname{dom}} g^* = \overline{\operatorname{ran}}\,\partial f + \overline{\operatorname{ran}}\,\partial g$". It follows from $\operatorname{ran}\partial f = \operatorname{dom}\partial f^*$ (Bauschke–Combettes, Corollary 16.30) and the density of $\operatorname{dom}\partial f^*$ in $\operatorname{dom} f^*$ (Brøndsted–Rockafellar; Bauschke–Combettes, Corollary 16.39, applied to $f^* \in \Gamma_0(X)$).
--
--   **Formalization note.** $f$ is an `X → EReal` function satisfying the published `GammaZero`; $f^*$ is `conj f`, $\operatorname{dom} f^*$ is `domConj f`, $\partial f$ is `subgrad f` and $\operatorname{ran}$ is the published `ran`. `CompleteSpace X` makes $X$ a Hilbert space.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (2021), p. 28, proof of Theorem 6.9 (first line); cf. Bauschke–Combettes, Convex Analysis and Monotone Operator Theory, Corollaries 16.30 and 16.39

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization

namespace InconsistentDR.Shadow

open MoreauProx.Characterization

/-- Proof of Theorem 6.9, p. 28 (via [6, Corollaries 16.30 and 16.39]): for `f ∈ Γ₀(X)`,
`cl dom f* = cl ran ∂f`. -/
theorem closure_domConj_eq_closure_ran_subgrad {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X]
    (f : X → EReal) (hf : GammaZero f) :
    closure (domConj f) = closure (ran (subgrad f)) := by sorry

end InconsistentDR.Shadow
