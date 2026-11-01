-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_edom_subset_closure_dom_subgrad
-- name    : InconsistentDR.Shadow.edom_subset_closure_dom_subgrad
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T23:32:02.904532+00:00
-- url     : https://prove2.me/theorems/3113c8dd-5dec-433a-bb66-64514f74c0f3
-- title:
--   $\operatorname{dom} f\subseteq\overline{\operatorname{dom}}\,\partial f$ for $f\in\Gamma_0(X)$ (Brøndsted–Rockafellar density, used in (68), p. 22)
-- statement:
--   Let $X$ be a real Hilbert space and let $f\in\Gamma_0(X)$ be a proper, convex, lower semicontinuous function $X\to\,]-\infty,+\infty]$, with subdifferential $\partial f$ and proximal mapping $P=(\mathrm{Id}+\partial f)^{-1}$. Then the domain of the subdifferential is dense in the effective domain of $f$:
--   $$\operatorname{dom} f\subseteq\overline{\operatorname{dom}\,\partial f}.$$
--   Since $\operatorname{dom}\partial f\subseteq\operatorname{dom}f$, this gives $\overline{\operatorname{dom}}\,\partial f=\overline{\operatorname{dom}}\,f$.
--
--   This is the Brøndsted–Rockafellar density theorem (Bauschke–Combettes, Corollary 16.39). In the paper it is what allows (68) to write $v_D=P_{\overline{\operatorname{dom} f-\operatorname{dom} g}}(0)$ for $D=\operatorname{dom}\partial f-\operatorname{dom}\partial g$, and hence to apply (70) to pairs $(a,b)\in\operatorname{dom}f\times\operatorname{dom}g$ in Lemma 6.3.
--
--   **Formalization Note** $f$ is an `X → EReal` function satisfying the published `GammaZero`; $\partial f$ is `subgrad f`, $\operatorname{dom}$ of an operator is the published `dom`, and $\operatorname{dom} f=\{x: f(x)<+\infty\}$ is `edom f`. The proximal map is supplied as a map `P` with `IsResolvent 1 (subgrad f) P`, the standing setting of the mission (it exists for every $f\in\Gamma_0(X)$ by Minty's theorem); it is used only to guarantee that $\partial f$ is nonempty somewhere.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (2021), p. 22, display (68) (the identification v_D = P of 0 onto cl(dom f − dom g)); Bauschke–Combettes, Convex Analysis and Monotone Operator Theory in Hilbert Spaces, Corollary 16.39 (Brøndsted–Rockafellar)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_InconsistentDR_Shadow_Optimization

namespace InconsistentDR.Shadow

open ThreeOpSplitting.Convergence MoreauProx.Characterization

/-- (68), p. 22 (via [6, Corollary 16.39], Brøndsted–Rockafellar): for `f ∈ Γ₀(X)` (here with a
proximal map `P = (Id + ∂f)⁻¹`), `dom f ⊆ cl dom ∂f`. -/
theorem edom_subset_closure_dom_subgrad {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (f : X → EReal) (hf : GammaZero f) (P : X → X)
    (hP : IsResolvent 1 (subgrad f) P) :
    edom f ⊆ closure (dom (subgrad f)) := by sorry

end InconsistentDR.Shadow
