-- Prove2me | Theorems.Thm_OAI_MainGap_first_pair_choice
-- name    : OAI.MainGap.first_pair_choice
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:21:46.642468+00:00
-- url     : https://prove2.me/theorems/f4c742c1-e486-41b4-ad54-37d84dc34752
-- title:
--   First pair choice: two contractions with $T_iT_j^*=\delta_{ij}\,\rho_{\eta,2\eta}(d)$ from a comparison $d\oplus d\precsim v$
-- statement:
--   Let $A$ be a C*-algebra (not necessarily unital) with its usual order. Notation:
--
--   - $\operatorname{Her}(x)=\overline{xAx^*}$ is the norm closure of $\{xax^*: a\in A\}$.
--   - $\operatorname{diag}_2(d)\precsim(v)$ means that there are rows $(r_{j,1},r_{j,2})$ in $A^2$ with $r_{j,p}^*\,v\,r_{j,q}\to\delta_{pq}\,d$ in norm as $j\to\infty$, for $p,q\in\{1,2\}$ (finite Cuntz comparison of $\operatorname{diag}(d,d)\in M_2(A)$ with $v\in M_1(A)$).
--   - For $\eta>0$, $\rho_{\eta,2\eta}(t)=\min\big(1,\max(t-\eta,0)/\eta\big)$, and $\rho_{\eta,2\eta}(d)$ is obtained by continuous functional calculus.
--
--   **Theorem.** Let $d,v,k\in A$ with $d\ge0$, $v\ge0$, $\operatorname{diag}_2(d)\precsim(v)$, $d\in\operatorname{Her}(k)$ and $v\in\operatorname{Her}(k)$, and let $\eta>0$. Then there exist $T_0,T_1\in A$ such that for all $i,j\in\{0,1\}$:
--   1. $\|T_i\|\le1$;
--   2. $T_i\in\operatorname{Her}(k)$;
--   3. $T_iT_j^*=\rho_{\eta,2\eta}(d)$ if $i=j$, and $T_iT_j^*=0$ if $i\neq j$;
--   4. $T_i^*T_j\in\operatorname{Her}(v)$.
--
--   In particular
--
--   $$
--   T_0T_0^*=T_1T_1^*=\rho_{\eta,2\eta}(d),\qquad T_0T_1^*=T_1T_0^*=0.
--   $$
--
--   So the comparison $d\oplus d\precsim v$ produces two contractions inside $\operatorname{Her}(k)$ that carry two orthogonal copies of the cut-off $\rho_{\eta,2\eta}(d)$, with all products $T_i^*T_j$ under $v$. Such pairs supply the first two members of a four-element choice in the argument towards strong pure infiniteness.
--
--   **Formalization Note** The pair is `T : Fin 2 → A`; the hypothesis is `FiniteCuntzLE (diagonalCorner 2 d) (scalarCorner v)`, and $\rho_{\eta,2\eta}(d)$ is `ramp d η (2*η)`. The order on $A$ is `CStarAlgebra.spectralOrder`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/ChoicePairs.lean#L38-L67

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

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.choicePairsPartialOrder
attribute [local instance] OAI.MainGap.choicePairsStarOrderedRing
variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem OAI.MainGap.first_pair_choice {d v k : A} (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hdv : FiniteCuntzLE (diagonalCorner 2 d) (scalarCorner v))
    (hdk : d ∈ Her k) (hvk : v ∈ Her k) {η : ℝ} (hη : 0 < η) :
    ∃ T : Fin 2 → A,
      (∀ i, ‖T i‖ ≤ 1) ∧ (∀ i, T i ∈ Her k) ∧
      (∀ i j, T i * star (T j) = if i=j then ramp d η (2*η) else 0) ∧
      (∀ i j, star (T i) * T j ∈ Her v) := by sorry
