-- Prove2me | Theorems.Thm_NCPSeqOpt_AugLag_Supplement_theorem_7_2
-- name    : NCPSeqOpt.AugLag.Supplement.theorem_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:53:52.249954+00:00
-- url     : https://prove2.me/theorems/b0756ef7-c9ac-4b30-9189-3858f1d72e9b
-- title:
--   Theorem 7.2, p. 21 — X-regularity is the weakest strict CQ for X ∈ {CAKKT, AKKT, AGP, TAKKT}: X-regular ⇔ (X ⇒ KKT for every C¹ objective)
-- statement:
--   Let $G:\mathbb R^n\to\mathbb E$ be continuously differentiable, $\mathcal K\subseteq\mathbb E$ a nonempty closed convex cone, and $\bar x$ a feasible point of (NCP), $G(\bar x)\in\mathcal K$. Then:
--
--   1. $\bar x$ satisfies CAKKT-regularity if and only if, for every continuously differentiable $f:\mathbb R^n\to\mathbb R$, the CAKKT condition at $\bar x$ (for the objective $f$) implies the KKT conditions at $\bar x$;
--   2. the same equivalence holds for AKKT-regularity and the AKKT condition (Definition 5.1);
--   3. the same equivalence holds for AGP-regularity and the AGP condition (Definition 3.2);
--   4. the same equivalence holds for TAKKT-regularity and the TAKKT condition (Definition 3.1).
--
--   In symbols, for each $X\in\{\mathrm{CAKKT},\mathrm{AKKT},\mathrm{AGP},\mathrm{TAKKT}\}$,
--   $$X\text{-regularity at }\bar x\iff\Big(\forall f\in C^1(\mathbb R^n):\ X\text{ at }\bar x\ \Rightarrow\ \text{KKT at }\bar x\Big).$$
--
--   Each regularity condition is therefore the weakest strict constraint qualification associated with its sequential optimality condition: any algorithm whose limit points satisfy $X$ converges to KKT points under $X$-regularity, and under no weaker condition of this kind.
--
--   **Formalization Note** $X$-regularity is outer semicontinuity of $(x,r)\mapsto\mathbb K_X(x,r)$ at $(\bar x,0)$ with the sequential outer limit in $\mathbb R^n\times\mathbb R$. $\mathcal K$ and $G$ are fixed; only the objective $f$ varies. The paper's "Similar conclusions are valid for AKKT-, AGP-, and TAKKT-regularity" is stated as the last three conjuncts.
--
--   Differences from the source:
--   - encoding: |y| in 𝕂_A → ‖y‖; reason: y ∈ 𝔼, so the absolute value can only be the norm.
-- source:
--   Andreani, Gómez, Haeser, Mito & Ramos, On Optimality Conditions for Nonlinear Conic Programming, author's manuscript (revised 2021-04-20; Math. Oper. Res. doi:10.1287/moor.2021.1203), Theorem 7.2, p. 21 (Definition 7.1, p. 21; Definitions 3.1–3.3, pp. 5–7; Definition 5.1, p. 12)

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_NCPSeqOpt_AugLag_Supplement_Setting

namespace NCPSeqOpt.AugLag.Supplement

open MoreauProx.Decomposition NCPSeqOpt.AugLag
open scoped InnerProductSpace
open Filter Topology

theorem theorem_7_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ}
    (G : EuclideanSpace ℝ (Fin n) → E) (hG : ContDiff ℝ 1 G)
    (K : Set E) (hK : IsClosedConvexCone K)
    (xbar : EuclideanSpace ℝ (Fin n)) (hfeas : G xbar ∈ K) :
    (IsCAKKTRegular G K xbar ↔ ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f →
        IsCAKKT f G K xbar → IsKKT f G K xbar) ∧
    (IsAKKTRegular G K xbar ↔ ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f →
        IsAKKT f G K xbar → IsKKT f G K xbar) ∧
    (IsAGPRegular G K xbar ↔ ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f →
        IsAGP f G K xbar → IsKKT f G K xbar) ∧
    (IsTAKKTRegular G K xbar ↔ ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f →
        IsTAKKT f G K xbar → IsKKT f G K xbar) := by sorry

end NCPSeqOpt.AugLag.Supplement
