-- Prove2me | Theorems.Thm_OAI_MainGap_four_fixed_impossible
-- name    : OAI.MainGap.four_fixed_impossible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:24:29.828631+00:00
-- url     : https://prove2.me/theorems/4be5a8dc-3b90-46d8-ba80-f0f38ccbb421
-- title:
--   The exact four-element choice conditions are inconsistent in a unital C*-algebra
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
--   **Theorem.** Let $X\in A$ with $X\ge0$, and let $B_0,B_1,B_2,B_3\in A$. Then the following conditions cannot all hold:
--   1. $V_X\neq0$;
--   2. $B_0B_0^*\le\tfrac12\cdot1$, $\ B_1B_1^*=B_0B_0^*$, and $B_0B_1^*=0$;
--   3. $H_XB_0^*=B_0^*$ and $H_XB_1^*=B_1^*$;
--   4. $U_X(B_0)=0$;
--   5. $B_2B_2^*\le\tfrac12\cdot1$, $\ B_2^*B_3=0$, and $B_2^*B_2=B_3^*B_3$;
--   6. $R_X(B_0,B_2)=0$;
--   7. $\rho_{0,1/2}\big(P_X(B_0)\big)\,B_3=B_3$.
--
--   This is the exact, single-algebra form of an obstruction. Conditions 2 to 4 describe a first pair $B_0,B_1$ with equal left moduli, $B_0B_1^*=0$, adjoints fixed by $H_X$, and (through condition 4) $B_0B_0^*$ acting as $\tfrac12$ on $X_1$; conditions 5 to 7 describe a second pair $B_2,B_3$ with equal right moduli, $B_2^*B_3=0$, $B_2B_2^*$ acting as $\tfrac12$ on the cut-down $X_2(B_0)$, and $B_3$ supported under the defect $P_X(B_0)$ left by the first pair. The theorem shows that these requirements are incompatible as soon as $V_X\neq0$. An approximate version along ultralimits of representations is reduced to this statement.
--
--   **Formalization Note** The elements are `firstX`, `firstV`, `firstH`, `firstK`, `firstU`, `firstR`, `scalingDefect`, `prospectiveDefect`, `lastX`, `lastR`, and $\delta$ is `deficiency`; $\sqrt{1-H^2}$ is `CFC.sqrt (1 - H * H)`. The four elements are `B : Fin 4 → A`, the conclusion is `False`, and the order on $A$ is `CStarAlgebra.spectralOrder`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Defect.lean#L153-L210

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

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.fourFixedOrder
attribute [local instance] OAI.MainGap.fourFixedStarOrder
variable {A : Type*} [CStarAlgebra A]

theorem OAI.MainGap.four_fixed_impossible {X : A} (hX : 0 ≤ X) (B : Fin 4 → A)
    (hV : firstV X ≠ 0)
    (hD : B 0 * star (B 0) ≤ (1/2 : ℝ) • (1 : A))
    (hmod : B 1 * star (B 1) = B 0 * star (B 0))
    (hcross : B 0 * star (B 1) = 0)
    (hHB₀ : firstH X * star (B 0) = star (B 0))
    (hHB₁ : firstH X * star (B 1) = star (B 1))
    (hU : firstU X (B 0) = 0)
    (hD₃ : B 2 * star (B 2) ≤ (1/2 : ℝ) • (1 : A))
    (hc₃ : star (B 2) * B 3 = 0)
    (hm₃ : star (B 2) * B 2 = star (B 3) * B 3)
    (hR : lastR X (B 0) (B 2) = 0)
    (hs₃ : ramp (prospectiveDefect X (B 0)) 0 (1/2) * B 3 = B 3) : False := by sorry
