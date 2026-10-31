-- Prove2me | Theorems.Thm_GMFGLearn_eq_18
-- name    : GMFGLearn.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:21.546012+00:00
-- url     : https://prove2.me/theorems/4e4f077e-3197-4945-b6cc-0ce759dff5f3
-- title:
--   (18) — $W_1(\Gamma(\mathcal L_1),\Gamma(\mathcal L_2))\le(d_1d_2+d_3)W_1(\mathcal L_1,\mathcal L_2)$
-- statement:
--   Let $\mathcal S,\mathcal A$ be compact metric spaces, let $\Gamma_1:\mathcal P(\mathcal S\times\mathcal A)\to\Pi$ satisfy Assumption 1 with constant $d_1$, and let the GMFG satisfy Assumption 2 with constants $d_2,d_3$. Then for all $\mathcal L_1,\mathcal L_2\in\mathcal P(\mathcal S\times\mathcal A)$, with $\Gamma(\mathcal L)=\Gamma_2(\Gamma_1(\mathcal L),\mathcal L)$,
--
--   $$
--   W_1(\Gamma(\mathcal L_1),\Gamma(\mathcal L_2))\le(d_1d_2+d_3)\,W_1(\mathcal L_1,\mathcal L_2).
--   $$
--
--   For $d_1d_2+d_3<1$ this makes $\Gamma$ a contraction, the hypothesis of the Banach fixed-point theorem in Theorem 1.
--
--   Differences from the source:
--   - generalization: compact S ⊆ ℝ^d, A ⊆ ℝ^p → nonempty compact metric spaces with Borel σ-fields; reason: §2.1 states compact metric spaces; Euclidean subsets are an instance
--   - generalization: Γ₁ the optimal-policy selection → any map Γ₁ : P(S×A) → Π satisfying (13); reason: (18) uses only (13), (16), (17) and the triangle inequality; the selection of Step A is such a map
--   - encoding: reward law R(s,a,L) ∈ P([0,Rmax]) → measurable mean reward r̄(s,a,L) ∈ [0,Rmax]; reason: (18) involves only Γ₂, which does not depend on the reward; every such r̄ is the mean of R = δ_r̄
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, proof of Theorem 1, (18), p.9

import Mathlib
import Definitions.Def_GMFGLearn_GMFG

open MeasureTheory

namespace GMFGLearn

/-- **`Γ` is `(d₁d₂ + d₃)`-Lipschitz in `W₁` (18).** Guo–Hu–Xu–Zhang, *A General Framework for
Learning Mean-Field Games*, arXiv:2003.06069v3, (18), p.9: for any `L₁, L₂ ∈ P(S × A)`,
`W₁(Γ(L₁),Γ(L₂)) ≤ W₁(Γ₂(Γ₁(L₁),L₁),Γ₂(Γ₁(L₂),L₁)) + W₁(Γ₂(Γ₁(L₂),L₁),Γ₂(Γ₁(L₂),L₂))
≤ (d₁d₂ + d₃)W₁(L₁,L₂)`.

**Formalization Note** Under Assumptions 1 and 2, for any map `Γ₁ : P(S × A) → Π` satisfying (13)
(optimality of the selected policy is not used). No bound `d₁d₂ + d₃ < 1` is needed. -/
theorem eq_18 {S A : Type*}
    [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nonempty A]
    (M : GMFG S A) (Γ₁ : ProbabilityMeasure (S × A) → Policy S A) (d₁ d₂ d₃ : ℝ)
    (hA1 : Assumption1 Γ₁ d₁) (hA2 : Assumption2 M d₂ d₃)
    (L₁ L₂ : ProbabilityMeasure (S × A)) :
    W1 dSA (M.Gamma Γ₁ L₁) (M.Gamma Γ₁ L₂) ≤ (d₁ * d₂ + d₃) * W1 dSA L₁ L₂ := by sorry

end GMFGLearn
