-- Prove2me | Theorems.Thm_OAI_MainGap_four_limit_impossible
-- name    : OAI.MainGap.four_limit_impossible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:26:28.420051+00:00
-- url     : https://prove2.me/theorems/f80293ca-3682-4798-be11-451b3168f09b
-- title:
--   Asymptotic four-element choice conditions along an ultrafilter of representations are contradictory
-- statement:
--   Let $A$ be a unital C*-algebra with its usual order; all functions of self-adjoint elements below are taken in the continuous functional calculus. For a self-adjoint $a$ and reals $\varepsilon$ and $l<u$ write
--
--   - $(a-\varepsilon)_+$ for $\max(t-\varepsilon,0)$ applied to $a$;
--   - $\rho_{l,u}(a)$ for $\rho_{l,u}(t)=\min\big(1,\max(t-l,0)/(u-l)\big)$ applied to $a$;
--   - $\delta(a)=(\tfrac12-a)_+$ for $\max(\tfrac12-t,0)$ applied to $a$.
--
--   For $X\in A$ and $B,C\in A$ define
--
--   $$
--   X_1=(X-\tfrac1{16})_+,\quad V_X=(X-\tfrac18)_+,\quad H_X=\rho_{3/32,\,1/8}(X),\quad K_X=\rho_{3/64,\,1/16}(X),
--   $$
--
--   $$
--   U_X(B)=X_1\,\delta(BB^*)^2\,X_1,\qquad r_X(B)=\sqrt2\,B^*H_X,\qquad \Sigma(H,r)=1-WW^*\ \text{ with }\ W=r+\sqrt{1-H^2},
--   $$
--
--   $$
--   P_X(B)=\rho_{0,1}\big(K_X\,\Sigma(H_X,r_X(B))\,K_X\big),\qquad X_2(B)=\big(P_X(B)-\tfrac12\big)_+,\qquad R_X(B,C)=X_2(B)\,\delta(CC^*)^2\,X_2(B).
--   $$
--
--   Here $\sqrt{1-H^2}$ denotes the positive square root (in the situations below $\|H\|\le1$, so $1-H^2\ge0$).
--
--   Let $\iota$ be an index set and $\omega$ an ultrafilter on $\iota$. For each $i\in\iota$ let $\mathcal{H}_i$ be a complex Hilbert space, $\pi_i:A\to B(\mathcal{H}_i)$ a unital $*$-representation, and $\xi_i\in\mathcal{H}_i$ a vector with $\|\xi_i\|\le1$; operators on $\mathcal{H}_i$ carry the usual order. A property holds *for $\omega$-almost all $i$* if the set of such $i$ belongs to $\omega$, and $\lim_{i\to\omega}a_i=0$ for real $a_i$ means that $\{i:|a_i|<\varepsilon\}\in\omega$ for every $\varepsilon>0$.
--
--   **Theorem.** Let $X\in A$ with $X\ge0$, and let $B_0,B_1,B_2,B_3\in A$. Then the following conditions cannot all hold:
--   1. $\|\pi_i(V_X)\,\xi_i\|\ge\tfrac18$ for $\omega$-almost all $i$;
--   2. for every $i$: $\pi_i(B_0)\pi_i(B_0)^*\le\tfrac12\cdot1$, $\ \pi_i(B_1B_1^*)=\pi_i(B_0B_0^*)$, $\ \pi_i(B_0B_1^*)=0$, $\ \pi_i(H_XB_0^*)=\pi_i(B_0^*)$ and $\pi_i(H_XB_1^*)=\pi_i(B_1^*)$;
--   3. for every $w\in A$: $\lim_{i\to\omega}\|\pi_i(U_X(B_0)\,w\,V_X)\|=0$;
--   4. for every $i$: $\pi_i(B_2)\pi_i(B_2)^*\le\tfrac12\cdot1$, $\ \pi_i(B_2^*B_3)=0$ and $\pi_i(B_2^*B_2)=\pi_i(B_3^*B_3)$;
--   5. $\lim_{i\to\omega}\|\pi_i(R_X(B_0,B_2))\|=0$;
--   6. for every $i$: $\pi_i\big(\rho_{0,1/2}(P_X(B_0))\,B_3\big)=\pi_i(B_3)$.
--
--   In particular, conditions 3 and 5 are the asymptotic requirements
--
--   $$
--   \lim_{i\to\omega}\big\|\pi_i\big(U_X(B_0)\,w\,V_X\big)\big\|=0\ \ (w\in A),\qquad \lim_{i\to\omega}\big\|\pi_i\big(R_X(B_0,B_2)\big)\big\|=0.
--   $$
--
--   This is the approximate version of the four-element obstruction: the algebraic identities are required only after applying each representation, and two of the conditions only in the limit along $\omega$. The theorem shows that such configurations still cannot exist. It is used to show that suitably chosen quadruples cannot be matched, in all representations in which $X$ has large norm, by one fixed quadruple $B_0,\dots,B_3$.
--
--   **Formalization Note** The representations are `π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i)`; limits are `Tendsto _ (ω : Filter ι) (𝓝 0)` and condition 1 is an `∀ᶠ i in ω` statement. The auxiliary elements are `firstV`, `firstH`, `firstU`, `lastR`, `prospectiveDefect`, `ramp`, as defined above; the four elements are `B : Fin 4 → A` and the conclusion is `False`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Avoidance.lean#L25-L85

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
open Filter
open scoped Topology
universe u v
attribute [local instance] OAI.MainGap.avoidanceLimitPartialOrder
attribute [local instance] OAI.MainGap.avoidanceLimitStarOrderedRing
attribute [local instance] OAI.MainGap.avoidanceLimitOperatorPartialOrder
attribute [local instance] OAI.MainGap.avoidanceLimitOperatorStarOrderedRing
variable {ι : Type*} {A : Type u} [CStarAlgebra A]
variable {H : ι → Type v} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

theorem OAI.MainGap.four_limit_impossible (ω : Ultrafilter ι)
    (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (ξ : ∀ i, H i) (hξ : ∀ i, ‖ξ i‖ ≤ 1)
    {X : A} (hX : 0 ≤ X) (B : Fin 4 → A)
    (hV : ∀ᶠ i in (ω : Filter ι), (1/8 : ℝ) ≤ ‖π i (firstV X) (ξ i)‖)
    (hD₁ : ∀ i, π i (B 0) * star (π i (B 0)) ≤ (1/2 : ℝ) • 1)
    (hm₁ : ∀ i, π i (B 1 * star (B 1)) = π i (B 0 * star (B 0)))
    (hc₁ : ∀ i, π i (B 0 * star (B 1)) = 0)
    (hs₀ : ∀ i, π i (firstH X * star (B 0)) = π i (star (B 0)))
    (hs₁ : ∀ i, π i (firstH X * star (B 1)) = π i (star (B 1)))
    (hU : ∀ w : A, Tendsto (fun i => ‖π i (firstU X (B 0) * w * firstV X)‖)
      (ω : Filter ι) (𝓝 0))
    (hD₃ : ∀ i, π i (B 2) * star (π i (B 2)) ≤ (1/2 : ℝ) • 1)
    (hc₃ : ∀ i, π i (star (B 2) * B 3) = 0)
    (hm₃ : ∀ i, π i (star (B 2) * B 2) = π i (star (B 3) * B 3))
    (hR : Tendsto (fun i => ‖π i (lastR X (B 0) (B 2))‖) (ω : Filter ι) (𝓝 0))
    (hs₃ : ∀ i, π i (ramp (prospectiveDefect X (B 0)) 0 (1/2) * B 3) = π i (B 3)) : False := by sorry
