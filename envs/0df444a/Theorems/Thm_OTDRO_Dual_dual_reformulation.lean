-- Prove2me | Theorems.Thm_OTDRO_Dual_dual_reformulation
-- name    : OTDRO.Dual.dual_reformulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:31.002099+00:00
-- url     : https://prove2.me/theorems/c3e96aba-4faa-42ce-9394-d439b2a4a07a
-- title:
--   Theorem 1, p. 10 — Mahalanobis transport dual reformulation and attainment
-- statement:
--   Let $P_0$ be a Borel probability law on $\mathbb R^d$. Let $A$ satisfy Assumption 1, let $\delta>0$, and let $B\subseteq\mathbb R^d$ be convex. For a decision $\beta\in B$, suppose $\ell:\mathbb R\to\mathbb R$ is upper semicontinuous and $x\mapsto\ell(\beta^{\mathsf T}x)$ is integrable under $P_0$. The worst case over transport plans of cost at most $\delta$ satisfies
--
--   $$\sup_{P:\,D_c(P_0,P)\le\delta}E_P[\ell(\beta^{\mathsf T}X)]=\inf_{\lambda\ge0}f_\delta(\beta,\lambda).$$
--
--   Moreover, some $\lambda^*\ge0$ attains the infimum: $f_\delta(\beta,\lambda^*)=\inf_{\lambda\ge0}f_\delta(\beta,\lambda)$. The reformulation expresses the worst-case loss through an expectation under the baseline law and a one dimensional dual search.
--
--   **Formalization Note** The left side uses the paper's equivalent coupling linear program from §2.1. Both sides live in the extended reals. Integrability of $\ell(\beta^{\mathsf T}X)$ is stated explicitly because the cited strong duality theorem [6, Theorem 1] requires it; Theorem 1 on p. 10 omits this condition. The standing convexity of $B$ and $\beta\in B$ are retained.
-- source:
--   arXiv:1810.02403v3, Theorem 1, p. 10; §5.1 proof, p. 32

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting
import Definitions.Def_ModelRiskOT_Duality_primalValue

namespace OTDRO.Dual

open MeasureTheory

/-- Theorem 1, p. 10: the Mahalanobis-transport worst-case loss has the one-dimensional
dual representation, and the dual infimum is attained for decisions in `B`. -/
theorem dual_reformulation {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (hℓ : UpperSemicontinuous ℓ)
    (δ : ℝ) (hδ : 0 < δ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (β : EuclideanSpace ℝ (Fin d)) (hβ : β ∈ B)
    (hint : Integrable (fun x => ℓ (inner ℝ β x)) P0) :
    ModelRiskOT.Duality.primalValue (mahalCost A) (fun x => ℓ (inner ℝ β x)) P0 δ =
        ⨅ lam ∈ Set.Ici (0 : ℝ), fDelta P0 ℓ A δ β lam ∧
      ∃ lamStar : ℝ, 0 ≤ lamStar ∧
        fDelta P0 ℓ A δ β lamStar =
          ⨅ lam ∈ Set.Ici (0 : ℝ), fDelta P0 ℓ A δ β lam := by sorry

end OTDRO.Dual
