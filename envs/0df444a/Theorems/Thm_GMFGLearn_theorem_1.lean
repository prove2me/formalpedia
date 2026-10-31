-- Prove2me | Theorems.Thm_GMFGLearn_theorem_1
-- name    : GMFGLearn.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:23.782397+00:00
-- url     : https://prove2.me/theorems/4e155f7d-636d-4f6f-a7c4-8dc8eb88462a
-- title:
--   Theorem 1 — existence and uniqueness of the stationary GMFG solution (corrected: unique among equilibria whose policy is the selected $\Gamma_1(\mathcal L)$)
-- statement:
--   Let $\mathcal S,\mathcal A$ be compact metric spaces and $\Gamma_1$ an optimal-policy selection of a GMFG. Assume Assumption 1 (constant $d_1$), Assumption 2 (constants $d_2,d_3$) and $d_1d_2+d_3<1$. Then:
--
--   1. there is exactly one $\mathcal L\in\mathcal P(\mathcal S\times\mathcal A)$ such that $(\Gamma_1(\mathcal L),\mathcal L)$ is a stationary Nash equilibrium;
--   2. equivalently, $\Gamma(\mathcal L)=\Gamma_2(\Gamma_1(\mathcal L),\mathcal L)$ has exactly one fixed point.
--
--   This is the equilibrium the learning algorithm GMF-V approximates (Theorem 2).
--
--   Differences from the source:
--   - correction: "there exists a unique stationary NE" → exactly one L with (Γ₁(L), L) a stationary NE, and exactly one fixed point of Γ; reason: without the selection uniqueness fails: S = {0}, A = {0,1}, P ≡ δ₀, r ≡ 0 satisfies the assumptions with d₁ = 0, d₂ = 1, d₃ = 1/2, and (δ₀-policy, δ₀⊗δ₀), (uniform, δ₀⊗uniform) are two stationary NEs; Remark 1(1) specifies the selection rule
--   - generalization: compact S ⊆ ℝ^d, A ⊆ ℝ^p → nonempty compact metric spaces with Borel σ-fields; reason: §2.1 states compact metric spaces; Euclidean subsets are an instance
--   - encoding: reward law R(s,a,L) ∈ P([0,Rmax]) → measurable mean reward r̄(s,a,L) ∈ [0,Rmax]; reason: V and Definition 1 depend on R only through its mean, and every such r̄ is the mean of R = δ_r̄
--   - reading: "for any policy π" in Definition 1 → for every measurable policy π ∈ Π; reason: Π is the class Step A optimizes over ((12), p.8)
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, Theorem 1 and its proof, p.9; Remark 1(1), p.9

import Mathlib
import Definitions.Def_GMFGLearn_GMFG

open MeasureTheory

namespace GMFGLearn

/-- **Theorem 1 (existence and uniqueness of the stationary GMFG solution).** Guo–Hu–Xu–Zhang, *A
General Framework for Learning Mean-Field Games*, arXiv:2003.06069v3, Theorem 1, p.9: "Given
Assumptions 1 and 2, and assume d1d2 + d3 < 1. Then there exists a unique stationary NE to (GMFG)."
The proof concludes "there exists a unique fixed-point of Γ, or equivalently, a unique stationary
MFG solution".

**Formalization Note** Corrected: uniqueness holds among the equilibria whose policy is the
selected optimal policy `Γ₁(L)` (Remark 1(1), p.9: "we specify a rule in Step A to select one
optimal policy"). Without the selection two equilibria can coexist (S = {0}, A = {0,1}, P ≡ δ₀,
r ≡ 0, d₁ = 0, d₂ = 1, d₃ = 1/2: `(δ₀-policy, δ₀⊗δ₀)` and `(uniform, δ₀⊗uniform)`). Both clauses of
the proof's conclusion are stated: a unique `L` with `(Γ₁(L), L)` a stationary NE, and a unique
fixed point of `Γ`. -/
theorem theorem_1 {S A : Type*}
    [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nonempty A]
    (M : GMFG S A) (Γ₁ : ProbabilityMeasure (S × A) → Policy S A)
    (hΓ₁ : IsOptimalSelection M Γ₁) (d₁ d₂ d₃ : ℝ)
    (hA1 : Assumption1 Γ₁ d₁) (hA2 : Assumption2 M d₂ d₃) (hd : d₁ * d₂ + d₃ < 1) :
    (∃! L : ProbabilityMeasure (S × A), IsStationaryNE M (Γ₁ L) L) ∧
      (∃! L : ProbabilityMeasure (S × A), M.Gamma Γ₁ L = L) := by sorry

end GMFGLearn
