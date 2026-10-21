-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_vR_eq_zero_of_zero_mem_domConj
-- name    : InconsistentDR.Shadow.vR_eq_zero_of_zero_mem_domConj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:29.476925+00:00
-- url     : https://prove2.me/theorems/8ef5b400-8d04-4d33-bad7-2f66a1dd0b7e
-- title:
--   Proof of Theorem 6.9, p. 28 — 0 ∈ dom f* + dom g* forces v_R = P_{cl(ran ∂f + ran ∂g)}(0) = 0
-- statement:
--   Let $X$ be a real Hilbert space and $f, g \in \Gamma_0(X)$. Let $v_R$ be the projection of $0$ onto the closed convex set $\overline{\operatorname{ran}\partial f + \operatorname{ran}\partial g}$. If
--   $$0 \in \operatorname{dom} f^* + \operatorname{dom} g^*,$$
--   then $v_R = 0$.
--
--   This is the first step of the proof of the main theorem: the hypothesis on the conjugates, which is easy to check in applications, implies the standing assumption $v_R = 0$ of §6.
--
--   **Formalization Note** $f, g$ are `X → EReal` functions satisfying the published `GammaZero`; $\operatorname{dom} f^* = \{u \mid f^*(u) < +\infty\}$ with the published `conj`. $v_R$ is encoded as the least-norm point of the closure of $\operatorname{ran}\partial f + \operatorname{ran}\partial g$. The paper's step uses $\overline{\operatorname{dom}}\, f^* = \overline{\operatorname{ran}}\, \partial f$ (Brøndsted–Rockafellar) without comment; it is part of the proof, not a hypothesis. The standing assumption (12) is not needed here and is not assumed.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 28, proof of Theorem 6.9, first sentence

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_FRBSplitting_Weak_Setting
import Definitions.Def_InconsistentDR_Shadow_Operators
import Definitions.Def_InconsistentDR_Shadow_Optimization

namespace InconsistentDR.Shadow

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence MoreauProx.Characterization FRBSplitting.Weak

/-- Proof of Theorem 6.9, p. 28, first step: for `f, g ∈ Γ₀(X)`, if `0 ∈ dom f* + dom g*` then
`v_R = P_{cl(ran ∂f + ran ∂g)}(0) = 0`. -/
theorem vR_eq_zero_of_zero_mem_domConj {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → EReal) (hf : GammaZero f) (hg : GammaZero g)
    (vR : X) (hvR : IsMinNormPt (closure (setR (subgrad f) (subgrad g))) vR)
    (h0 : (0 : X) ∈ domConj f + domConj g) :
    vR = 0 := by sorry

end InconsistentDR.Shadow
