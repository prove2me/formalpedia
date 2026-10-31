-- Prove2me | Theorems.Thm_GraphonLabelGame_eq_6_1
-- name    : GraphonLabelGame.eq_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:38.562827+00:00
-- url     : https://prove2.me/theorems/955a922e-a5e8-4ea4-b77f-30ffa1e06888
-- title:
--   (6.1) — $\langle\mu,h\rangle=\frac1n\sum_i\mathbb E[h(U^n_i,X^n_i)]$ for conditional sampling on the intervals $I^n_i$
-- statement:
--   Let $E$ be a Polish space, $\mu\in\mathcal P_{\mathrm{Unif}}([0,1]\times E)$ and $n\ge1$. Suppose $(U^n_i,X^n_i)$, $i=1,\dots,n$, are random variables whose law is the conditional law of $(U,X)\sim\mu$ given $\{U\in I^n_i\}$, that is,
--   $$\mathcal L(U^n_i,X^n_i)=n\,\mu|_{I^n_i\times E}.$$
--   Then for every bounded measurable $h:[0,1]\times E\to\mathbb R$,
--   $$\langle\mu,h\rangle=\frac1n\sum_{i=1}^n\mathbb E\big[h(U^n_i,X^n_i)\big].$$
--
--   The identity says that the label-state law $\mu$ is the average of the $n$ players' laws; it is the starting point of the law of large numbers of Theorem 6.1.
--
--   Differences from the source:
--   - encoding: n ∈ ℕ → 0 < n; reason: the paper's ℕ starts at 1
--   - encoding: "the law of (Uⁿᵢ, Xⁿᵢ) is the conditional law of (U, X) given {U ∈ Iⁿᵢ}" → P ∘ (Uⁿᵢ, Xⁿᵢ)⁻¹ = n · μ|_{Iⁿᵢ × E}; reason: the conditional law given an event of probability 1/n
--   - encoding: Iⁿᵢ = [(i−1)/n, i/n) for i < n and Iⁿₙ = [(n−1)/n, 1] (2.1); §6.1 prints the half-open form for all i → I n i with i : Fin n counted from 0, the last interval closed; reason: (2.1) is the definition; the two forms differ by a null set
--   - encoding: the chain ⟨μ,h⟩ = E[h(U,X)] = Σᵢ ∫_{Iⁿᵢ} E[h(u,X) | U = u] du = Σᵢ ∫_{Iⁿᵢ} E[h(u,Xⁿᵢ) | Uⁿᵢ = u] du = (1/n) Σᵢ E[h(Uⁿᵢ,Xⁿᵢ)] → its first and last members, with (U, X) not carried; reason: the intermediate members are conditional expectations given null events (defined only up to versions) and are equal to the ends; (U, X) enters only through its law μ
--   - encoding: h : [0,1] × E → ℝ → h : ℝ × E → ℝ; reason: extension by 0; μ and the samples live on [0,1] × E
-- source:
--   Lacker, Soret, A Label-State Formulation of Stochastic Graphon Games and Approximate Equilibria on Large Networks, arXiv:2204.09642v1, §6.1, (6.1), p.24

import Mathlib
import Definitions.Def_GraphonLabelGame_Kernel

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GraphonLabelGame

/-- **(6.1)**. Lacker–Soret, arXiv:2204.09642v1, §6.1, (6.1), p.24.
Let `E` be Polish, `μ ∈ P_Unif([0, 1] × E)` and `n ≥ 1`. If `(Uⁿᵢ, Xⁿᵢ)`, `i ∈ [n]`, are random
variables such that the law of `(Uⁿᵢ, Xⁿᵢ)` is the conditional law of `(U, X) ∼ μ` given
`{U ∈ Iⁿᵢ}`, i.e. `n · μ|_{Iⁿᵢ × E}`, then for every bounded measurable `h : [0, 1] × E → ℝ`,
`⟨μ, h⟩ = (1/n) Σᵢ E[h(Uⁿᵢ, Xⁿᵢ)]`. -/
theorem eq_6_1 {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] (μ : PUnif E) (n : ℕ) (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Fin n → Ω → ℝ × E) (hY : ∀ i, Measurable (Y i))
    (hlaw : ∀ i, P.map (Y i) = (n : ℝ≥0∞) • (μ.1 : Measure (ℝ × E)).restrict (I n i ×ˢ univ))
    (h : ℝ × E → ℝ) (hmeas : Measurable h) (hbdd : ∃ C : ℝ, ∀ p, |h p| ≤ C) :
    ∫ p, h p ∂(μ.1 : Measure (ℝ × E)) = (1 / (n : ℝ)) * ∑ i, ∫ ω, h (Y i ω) ∂P := by sorry

end GraphonLabelGame
