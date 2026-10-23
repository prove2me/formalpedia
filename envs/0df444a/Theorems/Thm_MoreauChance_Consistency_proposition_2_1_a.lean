-- Prove2me | Theorems.Thm_MoreauChance_Consistency_proposition_2_1_a
-- name    : MoreauChance.Consistency.proposition_2_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:28.465226+00:00
-- url     : https://prove2.me/theorems/1f9a8843-214f-42ad-b542-b82dd862b64c
-- title:
--   Proposition 2.1 a), p. 5 — monotone convergence: e_λg ↗ g as λ ↘ 0
-- statement:
--   Let $\mathcal H$ be a separable real Hilbert space and $g:\mathcal H\to\mathbb R$ a convex, lower semicontinuous (real-valued) function. Write $\mathrm e_\lambda g(x)=\inf_z\{g(z)+\frac1{2\lambda}\|x-z\|^2\}$ for its Moreau envelope. Then for every $x\in\mathcal H$:
--
--   1. $\lambda\mapsto\mathrm e_\lambda g(x)$ is nonincreasing on $(0,\infty)$: $\mathrm e_{\lambda_1}g(x)\le\mathrm e_{\lambda_2}g(x)$ whenever $\lambda_1>\lambda_2>0$;
--   2. $\mathrm e_\lambda g(x)\le g(x)$ for every $\lambda>0$;
--   3. $$\lim_{\lambda\to0^+}\mathrm e_\lambda g(x)=g(x).$$
--
--   Together these say $\mathrm e_\lambda g(x)\nearrow g(x)$ as $\lambda\searrow0$. This is the basic approximation property that the paper transfers to the probability function and to the objective of the regularized problems.
--
--   **Formalization Note** The envelope is computed as an extended-real infimum; the limit is along $\lambda\to0$ with $\lambda>0$. Separability is the paper's standing assumption on $\mathcal H$ (§2.1).
-- source:
--   van Ackooij, Pérez-Aros, Soto & Vilches, Inner Moreau envelope of nonsmooth conic chance constrained optimization problems, arXiv:2301.09803v1, p. 5, Proposition 2.1 a)

import Mathlib
import Definitions.Def_MoreauChance_Consistency_Basic

open Filter Topology
open scoped InnerProductSpace

namespace MoreauChance.Consistency

theorem proposition_2_1_a
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (g : H → ℝ) (hg_convex : ConvexOn ℝ Set.univ g) (hg_lsc : LowerSemicontinuous g) (x : H) :
    (∀ l1 l2 : ℝ, 0 < l2 → l2 < l1 →
        moreauEnv (fun z => (g z : EReal)) l1 x ≤ moreauEnv (fun z => (g z : EReal)) l2 x) ∧
      (∀ l : ℝ, 0 < l → moreauEnv (fun z => (g z : EReal)) l x ≤ (g x : EReal)) ∧
      Tendsto (fun l => moreauEnv (fun z => (g z : EReal)) l x) (𝓝[>] 0) (𝓝 (g x : EReal)) := by sorry

end MoreauChance.Consistency
