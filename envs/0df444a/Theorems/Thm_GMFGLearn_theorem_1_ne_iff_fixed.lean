-- Prove2me | Theorems.Thm_GMFGLearn_theorem_1_ne_iff_fixed
-- name    : GMFGLearn.theorem_1_ne_iff_fixed
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:38.044982+00:00
-- url     : https://prove2.me/theorems/32a7bc9e-3cc0-47ee-84ae-f78b069a3ac1
-- title:
--   Proof of Theorem 1 — $(\Gamma_1(\mathcal L),\mathcal L)$ is a stationary NE iff $\mathcal L=\Gamma(\mathcal L)$ (corrected: for the selected policy $\Gamma_1(\mathcal L)$)
-- statement:
--   Let $\Gamma_1$ be an optimal-policy selection of a GMFG on compact metric spaces $\mathcal S,\mathcal A$, and $\Gamma(\mathcal L)=\Gamma_2(\Gamma_1(\mathcal L),\mathcal L)$. For every policy $\pi$ and every $\mathcal L\in\mathcal P(\mathcal S\times\mathcal A)$,
--
--   $$
--   \big((\pi,\mathcal L)\text{ is a stationary NE and }\pi=\Gamma_1(\mathcal L)\big)\iff\big(\mathcal L=\Gamma_2(\Gamma_1(\mathcal L),\mathcal L)\text{ and }\pi=\Gamma_1(\mathcal L)\big).
--   $$
--
--   This turns the search for an equilibrium into a fixed-point problem for $\Gamma$.
--
--   Differences from the source:
--   - correction: "(π,L) is a stationary NE iff L = Γ(L) and π = Γ₁(L)" → the equivalence for pairs with π = Γ₁(L); reason: the printed ⇒ is false: with S = {0}, A = {0,1}, P ≡ δ₀, r ≡ 0, every policy is optimal and (δ₀-policy, δ₀⊗δ₀) is a stationary NE whose policy differs from Γ₁(L) = uniform
--   - generalization: compact S ⊆ ℝ^d, A ⊆ ℝ^p → nonempty compact metric spaces with Borel σ-fields; reason: §2.1 states compact metric spaces; Euclidean subsets are an instance
--   - encoding: reward law R(s,a,L) ∈ P([0,Rmax]) → measurable mean reward r̄(s,a,L) ∈ [0,Rmax]; reason: V and Definition 1 depend on R only through its mean, and every such r̄ is the mean of R = δ_r̄
--   - reading: "for any policy π" in Definition 1 → for every measurable policy π ∈ Π; reason: Π is the class Step A optimizes over ((12), p.8)
-- source:
--   Guo, Hu, Xu, Zhang, A General Framework for Learning Mean-Field Games, arXiv:2003.06069v3, proof of Theorem 1, first sentence, p.9

import Mathlib
import Definitions.Def_GMFGLearn_GMFG

open MeasureTheory

namespace GMFGLearn

/-- **A selected pair `(Γ₁(L), L)` is a stationary NE iff `L = Γ(L)`.** Guo–Hu–Xu–Zhang, *A General
Framework for Learning Mean-Field Games*, arXiv:2003.06069v3, proof of Theorem 1, p.9: "First by
Definition 1 and the definitions of Γi (i = 1,2), (π,L) is a stationary NE iff L = Γ(L) =
Γ2(Γ1(L),L) and π = Γ1(L), where Γ(L) = Γ2(Γ1(L),L)."

**Formalization Note** Corrected: the printed "⇒" fails for an NE whose policy is a different
optimal policy than the selected `Γ₁(L)` (S = {0}, A = {0,1}, P ≡ δ₀, r ≡ 0: every pair
`(π, δ₀ ⊗ π(0))` is an NE). The equivalence is stated for `π = Γ₁(L)` on both sides, which is how
Theorem 1 uses it. `Γ₁` is any optimal-policy selection (12). -/
theorem theorem_1_ne_iff_fixed {S A : Type*}
    [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nonempty A]
    (M : GMFG S A) (Γ₁ : ProbabilityMeasure (S × A) → Policy S A)
    (hΓ₁ : IsOptimalSelection M Γ₁) (π : Policy S A) (L : ProbabilityMeasure (S × A)) :
    (IsStationaryNE M π L ∧ π = Γ₁ L) ↔ (L = M.Gamma2 (Γ₁ L) L ∧ π = Γ₁ L) := by sorry

end GMFGLearn
