-- Prove2me | Theorems.Thm_OAI_MainGap_last_pair_choice
-- name    : OAI.MainGap.last_pair_choice
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:22:54.737873+00:00
-- url     : https://prove2.me/theorems/a6a1aaf1-e303-43c4-ad4f-3abc98e48418
-- title:
--   Last pair choice: two orthogonal contractions from a properly infinite cut-down, of norm one wherever $\|\pi(R)\|\ge4\eta$
-- statement:
--   Let $A$ be a C*-algebra (not necessarily unital) with its usual order. Notation:
--
--   - $\operatorname{Her}(x)=\overline{xAx^*}$ is the norm closure of $\{xax^*: a\in A\}$.
--   - For self-adjoint $a$ and $\varepsilon\in\mathbb{R}$, $(a-\varepsilon)_+$ is $\max(t-\varepsilon,0)$ applied to $a$; for $l<u$, $\rho_{l,u}(t)=\min\big(1,\max(t-l,0)/(u-l)\big)$, applied by continuous functional calculus.
--   - An element $c\in A$ is *properly infinite* if there are rows $(r_{j,1},r_{j,2})$ in $A^2$ with $r_{j,p}^*\,c\,r_{j,q}\to\delta_{pq}\,c$ in norm for $p,q\in\{1,2\}$, i.e. $\operatorname{diag}(c,c)\in M_2(A)$ is finitely Cuntz-below $c\in M_1(A)$.
--
--   **Theorem.** Let $R,k\in A$ with $R\ge0$ and $R\in\operatorname{Her}(k)$, let $\eta>0$, and assume that $(R-\eta)_+$ is properly infinite. Put $t=\rho_{2\eta,4\eta}(R)$. Then there exist $T_0,T_1\in A$ such that for all $i,j\in\{0,1\}$:
--   1. $\|T_i\|\le1$;
--   2. $T_i\in\operatorname{Her}(k)$;
--   3. $T_i^*T_j=t^2$ if $i=j$, and $T_i^*T_j=0$ if $i\neq j$;
--   4. $T_iT_j^*\in\operatorname{Her}\big((R-\eta)_+\big)$;
--   5. for every C*-algebra $B$ and every $*$-homomorphism $\pi:A\to B$ with $\|\pi(R)\|\ge4\eta$, one has $\|\pi(T_i)\|=1$.
--
--   In particular
--
--   $$
--   T_0^*T_0=T_1^*T_1=\rho_{2\eta,4\eta}(R)^2,\qquad T_0^*T_1=T_1^*T_0=0.
--   $$
--
--   The two elements have equal and mutually orthogonal right moduli, ranges under $(R-\eta)_+$, and they do not degenerate in any representation in which $R$ has norm at least $4\eta$. Such pairs supply the last two members of a four-element choice in the argument towards strong pure infiniteness.
--
--   **Formalization Note** The pair is `T : Fin 2 → A`; `ProperlyInfinite (cut R η)` is the matrix-level condition `FiniteCuntzLE (doubleCorner c) (scalarCorner c)` for $c=(R-\eta)_+$; $t^2$ is `ramp R (2*η) (4*η) * ramp R (2*η) (4*η)`. In item 5, $B$ ranges over all (not necessarily unital) C*-algebras and $\pi$ over non-unital $*$-homomorphisms `A →⋆ₙₐ[ℂ] B`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/ChoicePairs.lean#L69-L100

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

theorem OAI.MainGap.last_pair_choice {R k : A} (hR : 0 ≤ R) (hRk : R ∈ Her k)
    {η : ℝ} (hη : 0 < η) (hp : ProperlyInfinite (cut R η)) :
    ∃ T : Fin 2 → A,
      (∀ i, ‖T i‖ ≤ 1) ∧ (∀ i, T i ∈ Her k) ∧
      (∀ i j, star (T i) * T j = if i=j then ramp R (2*η) (4*η) * ramp R (2*η) (4*η) else 0) ∧
      (∀ i j, T i * star (T j) ∈ Her (cut R η)) ∧
      (∀ {B : Type*} [NonUnitalCStarAlgebra B] (π : A →⋆ₙₐ[ℂ] B),
        4*η ≤ ‖π R‖ → ∀ i, ‖π (T i)‖ = 1) := by sorry
