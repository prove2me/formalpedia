-- Prove2me | Theorems.Thm_MPECRelax_KDBConv_display_15
-- name    : MPECRelax.KDBConv.display_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:16.679174+00:00
-- url     : https://prove2.me/theorems/7004322d-e728-4370-a9ea-28029e8b3b43
-- title:
--   Proof of Theorem 3.5, pp. 15–16, (15) — reduction to linearly independent gradients
-- statement:
--   Fix a point $x$ and the data of the MPEC (1). Suppose coefficients $\lambda\in\mathbb R^m$, $\mu\in\mathbb R^p$ and $\alpha,\beta,\eta^G,\eta^H\in\mathbb R^l$ satisfy
--   $$0=\nabla f(x)+\sum_{i}\lambda_i\nabla g_i(x)+\sum_j\mu_j\nabla h_j(x)-\sum_i(\alpha_i+\eta^G_i)\nabla G_i(x)-\sum_i(\beta_i+\eta^H_i)\nabla H_i(x)\tag{11}$$
--   with $\lambda,\alpha,\beta\ge 0$, the disjointness relations (13) and the sign relations (14). Then there are coefficients $\lambda',\mu',\alpha',\beta',\eta^{G\prime},\eta^{H\prime}$ such that
--
--   1. they satisfy (11) and $\lambda',\alpha',\beta'\ge 0$;
--   2. each support is contained in the corresponding original support: $\operatorname{supp}(\lambda')\subseteq\operatorname{supp}(\lambda)$, …, $\operatorname{supp}(\eta^{H\prime})\subseteq\operatorname{supp}(\eta^H)$ (so (12) and (13) persist);
--   3. they satisfy (14);
--   4. the gradients
--   $$\{\nabla g_i(x)\mid i\in\operatorname{supp}\lambda'\}\cup\{\nabla h_j(x)\mid j\in\operatorname{supp}\mu'\}\cup\{\nabla G_i(x)\mid i\in\operatorname{supp}\alpha'\cup\operatorname{supp}\eta^{G\prime}\}\cup\{\nabla H_i(x)\mid i\in\operatorname{supp}\beta'\cup\operatorname{supp}\eta^{H\prime}\}\tag{15}$$
--   are linearly independent.
--
--   In the paper this is the step "without loss of generality, cf. [34, Lem. A.1], we may assume that the gradients (15) are linearly independent": a Carathéodory-type reduction that keeps every property established so far and only shrinks the supports. The new coefficients are no longer KKT multipliers of the relaxed program.
--
--   **Formalization Note** The paper skips the standard constraints; since its WLOG must preserve them as well, the family (15) is extended by the gradients $\nabla g_i$ ($i\in\operatorname{supp}\lambda'$) and $\nabla h_j$ ($j\in\operatorname{supp}\mu'$). The gradient families are indexed by disjoint unions of subtypes. The statement is pointwise linear algebra and needs no differentiability hypothesis.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, pp. 15–16, proof of Theorem 3.5, display (15)

import Mathlib
import Definitions.Def_MPECRelax_KDBConv_Basic

open Filter Topology

namespace MPECRelax.KDBConv

/-- Proof of Theorem 3.5, pp. 15–16, the reduction to (15) ("without loss of generality,
cf. [34, Lem. A.1]"). At a point `x`, let coefficients `λ ≥ 0`, `µ`, `α ≥ 0`, `β ≥ 0`,
`η^G`, `η^H` satisfy (11) (standard constraints kept), (13) and (14). Then there are
coefficients `λ', µ', α', β', η^G', η^H'` (no longer KKT multipliers) with the same sign
constraints, supports contained in the original ones (so (12) and (13) persist),
satisfying (11) and (14), such that the family (15) extended by the standard-constraint
gradients,
`{∇g_i(x) | supp λ'} ∪ {∇h_j(x) | supp µ'} ∪ {∇G_i(x) | supp α' ∪ supp η^G'} ∪
{∇H_i(x) | supp β' ∪ supp η^H'}`, is linearly independent. -/
theorem display_15 {n m p l : ℕ} (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n)
    (lam : Fin m → ℝ) (mu : Fin p → ℝ) (α β ηG ηH : Fin l → ℝ)
    (h11 : gradient P.f x + ∑ i, lam i • gradient (P.g i) x + ∑ j, mu j • gradient (P.h j) x
        - ∑ i, α i • gradient (P.G i) x - ∑ i, β i • gradient (P.H i) x
        - ∑ i, ηG i • gradient (P.G i) x - ∑ i, ηH i • gradient (P.H i) x = 0)
    (hlam : ∀ i, 0 ≤ lam i) (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (h13 : Function.support α ∩ Function.support ηG = ∅ ∧
      Function.support β ∩ Function.support ηH = ∅ ∧
      Function.support ηG ∩ Function.support ηH = ∅)
    (h14 : (∀ i ∈ Function.support ηG ∩ Function.support β, 0 < ηG i) ∧
      (∀ i ∈ Function.support ηH ∩ Function.support α, 0 < ηH i)) :
    ∃ (lam' : Fin m → ℝ) (mu' : Fin p → ℝ) (α' β' ηG' ηH' : Fin l → ℝ),
      (gradient P.f x + ∑ i, lam' i • gradient (P.g i) x + ∑ j, mu' j • gradient (P.h j) x
        - ∑ i, α' i • gradient (P.G i) x - ∑ i, β' i • gradient (P.H i) x
        - ∑ i, ηG' i • gradient (P.G i) x - ∑ i, ηH' i • gradient (P.H i) x = 0) ∧
      (∀ i, 0 ≤ lam' i) ∧ (∀ i, 0 ≤ α' i) ∧ (∀ i, 0 ≤ β' i) ∧
      Function.support lam' ⊆ Function.support lam ∧
      Function.support mu' ⊆ Function.support mu ∧
      Function.support α' ⊆ Function.support α ∧ Function.support β' ⊆ Function.support β ∧
      Function.support ηG' ⊆ Function.support ηG ∧ Function.support ηH' ⊆ Function.support ηH ∧
      (∀ i ∈ Function.support ηG' ∩ Function.support β', 0 < ηG' i) ∧
      (∀ i ∈ Function.support ηH' ∩ Function.support α', 0 < ηH' i) ∧
      LinearIndependent ℝ
        (Sum.elim (fun i : ↥(Function.support lam') => gradient (P.g i.1) x)
          (Sum.elim (fun j : ↥(Function.support mu') => gradient (P.h j.1) x)
            (Sum.elim
              (fun i : ↥(Function.support α' ∪ Function.support ηG') => gradient (P.G i.1) x)
              (fun i : ↥(Function.support β' ∪ Function.support ηH') =>
                gradient (P.H i.1) x)))) := by sorry

end MPECRelax.KDBConv
