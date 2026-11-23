-- Prove2me | Theorems.Thm_NCPSeqOpt_AugLag_Supplement_remark_4
-- name    : NCPSeqOpt.AugLag.Supplement.remark_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:51:53.795022+00:00
-- url     : https://prove2.me/theorems/b69b1416-3348-4037-88a3-e9cfcee61cb6
-- title:
--   Remark 4, p. 21 (corrected: x̄ for the printed x) — at a feasible x̄ the four sets of Definition 7.1 at (x̄, 0) coincide, and KKT ⇔ −∇f(x̄) lies in each
-- statement:
--   Let $G:\mathbb R^n\to\mathbb E$ be continuously differentiable, $\mathcal K\subseteq\mathbb E$ a nonempty closed convex cone, and $\bar x$ a feasible point, $G(\bar x)\in\mathcal K$. Let $\mathbb K_A,\mathbb K_T,\mathbb K_{AGP},\mathbb K_C$ be the sets of Definition 7.1. Then:
--
--   1. all four sets at $(\bar x,0)$ coincide with
--   $$\{DG(\bar x)^*\Lambda:\ \langle\Lambda,G(\bar x)\rangle=0,\ \Lambda\in\mathcal K^\circ\};$$
--   2. for every continuously differentiable objective $f:\mathbb R^n\to\mathbb R$, the KKT conditions (7)–(8) hold at $\bar x$ if and only if $-\nabla f(\bar x)\in\mathbb K_A(\bar x,0)$, and likewise if and only if $-\nabla f(\bar x)$ lies in $\mathbb K_T(\bar x,0)$, in $\mathbb K_{AGP}(\bar x,0)$, and in $\mathbb K_C(\bar x,0)$.
--
--   This is the bridge used in the proof of Theorem 7.2: outer semicontinuity at $(\bar x,0)$ turns an approximate KKT sequence into membership of $-\nabla f(\bar x)$ in the set at $(\bar x,0)$, which is exactly KKT.
--
--   **Formalization Note** The sets are those of `NCPSeqOpt.AugLag.Supplement.Setting`; $\|y\|$ is used for the printed $|y|$ in $\mathbb K_A$.
--
--   Differences from the source:
--   - correction: the printed {DG(x)*Λ : ⟨Λ, G(x)⟩ = 0, Λ ∈ 𝒦°} and −∇f(x) → DG(x̄)*, G(x̄) and −∇f(x̄); reason: typo, the remark is about the sets at (x̄, 0) and x is not bound in it (source map rem-4).
--   - encoding: |y| in 𝕂_A → ‖y‖; reason: y ∈ 𝔼, so the absolute value can only be the norm.
-- source:
--   Andreani, Gómez, Haeser, Mito & Ramos, On Optimality Conditions for Nonlinear Conic Programming, author's manuscript (revised 2021-04-20; Math. Oper. Res. doi:10.1287/moor.2021.1203), Remark 4, p. 21 (Definition 7.1, p. 21; (7)–(8), p. 5)

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_NCPSeqOpt_AugLag_Supplement_Setting

namespace NCPSeqOpt.AugLag.Supplement

open MoreauProx.Decomposition NCPSeqOpt.AugLag
open scoped InnerProductSpace
open Filter Topology

theorem remark_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ}
    (G : EuclideanSpace ℝ (Fin n) → E) (hG : ContDiff ℝ 1 G)
    (K : Set E) (hK : IsClosedConvexCone K)
    (xbar : EuclideanSpace ℝ (Fin n)) (hfeas : G xbar ∈ K) :
    (KA G K xbar 0 = {w | ∃ Λ ∈ polarCone K, ⟪Λ, G xbar⟫_ℝ = 0 ∧ adjD G xbar Λ = w} ∧
      KT G K xbar 0 = {w | ∃ Λ ∈ polarCone K, ⟪Λ, G xbar⟫_ℝ = 0 ∧ adjD G xbar Λ = w} ∧
      KAGP G K xbar 0 = {w | ∃ Λ ∈ polarCone K, ⟪Λ, G xbar⟫_ℝ = 0 ∧ adjD G xbar Λ = w} ∧
      KC G K xbar 0 = {w | ∃ Λ ∈ polarCone K, ⟪Λ, G xbar⟫_ℝ = 0 ∧ adjD G xbar Λ = w}) ∧
    ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f →
      (IsKKT f G K xbar ↔ -gradient f xbar ∈ KA G K xbar 0) ∧
      (IsKKT f G K xbar ↔ -gradient f xbar ∈ KT G K xbar 0) ∧
      (IsKKT f G K xbar ↔ -gradient f xbar ∈ KAGP G K xbar 0) ∧
      (IsKKT f G K xbar ↔ -gradient f xbar ∈ KC G K xbar 0) := by sorry

end NCPSeqOpt.AugLag.Supplement
