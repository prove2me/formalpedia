-- Prove2me | Theorems.Thm_IndefPOMFG_lemma_5_5
-- name    : IndefPOMFG.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:37.371756+00:00
-- url     : https://prove2.me/theorems/364a1498-f38b-43d4-b1ea-40dc8805ad36
-- title:
--   Lemma 5.5 — 𝒥_i = 𝒥^P_i + ½⟨P₀x, x⟩ (corrected: Q̂^P, S̃^P, R̃^P of p.17)
-- statement:
--   Let (H1)–(H2) hold and $P\in\Upsilon([0,T];\mathbb S^n)$. For the initial value $x$ and every profile of square-integrable controls, in particular $(u^i,\bar u^{-i})$ with $u^i\in\mathscr U^i_c$,
--
--   $$\mathcal J_i(u^i,\bar u^{-i})=\mathcal J^P_i(u^i,\bar u^{-i})+\tfrac12\langle P_0x,x\rangle,$$
--
--   where $\mathcal J^P_i$ is the compensated $N$-player cost of p.17. The $N$-player costs and their compensated versions therefore order deviations identically (Remark 5.6).
--
--   Differences from the source:
--   - encoding: a complete filtered probability space carrying 2N independent d-dimensional Brownian motions Wⁱ, W̄ⁱ and a 1-dimensional W⁰, with 𝓕 their filtration augmented by the null sets (p.1) → every probability space with one standard Brownian motion of dimension 1+2Nd (independent coordinates), 𝓕 its natural filtration without augmentation; reason: independent coordinates are exactly 2N+1 independent Brownian motions of these dimensions; adapted processes of the augmented filtration have adapted modifications, and every quantity is an expectation
--   - encoding: "the solution" of a linear SDE ((2)–(4), (6)–(7), (10)–(13), (20), (42)–(43)) → every strong solution in the sense of Peng1990.SMP.SolvesSDE for the full filtration (statements quantify over solution processes); reason: solutions exist and are a.s. unique under (H1); quantifying over all of them is the paper's claim for each
--   - encoding: L^∞([0,T]; ·) = deterministic uniformly bounded functions (p.5), L²([0,T]; ·) square integrable → Borel functions of time bounded by a constant at every t ∈ [0,T] (L²: Borel and square integrable); reason: p.5's own definition; Borel measurability fixes the representative so coefficient-times-process integrands are progressive
--   - reading: σ̌ is non-degenerate ((H1), p.6) → |σ̌_t| ≥ κ > 0 for every t ∈ [0,T]; reason: σ̌ is scalar; the standard meaning in [19, Thm 7.16], which the paper invokes on p.3 for 𝓕^θ = 𝓕^{W⁰}
--   - reading: Υ([0,T]; 𝕊ⁿ) = {P : P_t = P₀ + ∫₀ᵗ Ṗ_s ds} (p.10), regularity of Ṗ not printed → P 𝕊ⁿ-valued on [0,T] with Ṗ Lebesgue integrable (P absolutely continuous); conditions involving Ṗ hold for some such representative Ṗ at every t; reason: the weakest reading of the printed set; Ṗ is determined only a.e.
--   - encoding: σᵀPσ + σ̄ᵀPσ̄ in M^P (23) and M̃^P (p.17), σ, σ̄ ∈ ℝ^{n×d} → tr(σᵀPσ) + tr(σ̄ᵀPσ̄); reason: the Itô correction of ⟨PX, X⟩ is the trace (App. B); for d = 1 the printed expression is this number
--   - correction: p.17: Q̂^P = −β₂S + B̄ᵀP + F̄ᵀPD and S̃^P = F̄ᵀPD̄ + α₂β₂S → Q̂^P = −β₂Sᵀ + B̄ᵀP + F̄ᵀPD and S̃^P = D̄ᵀPF̄ + α₂β₂S; reason: ill-typed for m ≠ n (S ∈ ℝ^{n×m}, Q̂^P ∈ ℝ^{m×n}; F̄ᵀPD̄ ∈ ℝ^{m×n}, S̃^P ∈ ℝ^{n×m}); these are the terms Itô's formula for ⟨Pxⁱ, xⁱ⟩ produces
--   - correction: p.17: R̃^P = β₁R + F̄ᵀPF̄ → R̃^P = β₁²R + F̄ᵀPF̄; reason: the cost (5) contributes β₁²⟨Ru⁽ᴺ⁾, u⁽ᴺ⁾⟩; counterexample to Lemma 5.5 as printed: n = m = d = N = 1, P = 0, R = σ̌ = 1, β₁ = 2, other data 0, u ≡ 1, T > 0: 𝒥_1 = T/2, printed 𝒥^P_1 = −T/2
--   - encoding: p.17: q̄^P = −α₁q + b̄ᵀPD̄ (a row vector) → q̄^P = −α₁q + D̄ᵀPb̄; reason: the same vector written as a column
--   - generalization: uⁱ ∈ 𝒰ⁱ_c with the other agents on ū (Lemma 5.5), P the relaxed compensator → every profile of IsCtrl controls (progressive, E sup|u|² < ∞) and every P ∈ Υ([0,T]; 𝕊ⁿ); reason: the identity is Itô's formula for ⟨P_t xⁱ_t, xⁱ_t⟩ and uses neither adaptedness to observations nor the decentralized profile; (uⁱ, ū⁻ⁱ) and the relaxed compensator are special cases
-- source:
--   Chen, Nie & Wu, Indefinite Linear-Quadratic Partially Observed Mean-Field Game, arXiv:2508.01568v1, Lemma 5.5, p.18 (𝒥^P_i and abbreviations p.17)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_IndefPOMFG_Coeffs
import Definitions.Def_IndefPOMFG_Space
import Definitions.Def_IndefPOMFG_NPlayer
import Definitions.Def_IndefPOMFG_Limiting
import Definitions.Def_IndefPOMFG_Compensator

open MeasureTheory Set Peng1990.SMP
open scoped NNReal ENNReal Matrix

namespace IndefPOMFG

/-- Lemma 5.5 (Chen–Nie–Wu, arXiv:2508.01568v1, p.18): for the initial value `x` and every
`P ∈ Υ([0, T]; 𝕊ⁿ)`, `𝒥_i(uⁱ, ū⁻ⁱ) = 𝒥^P_i(uⁱ, ū⁻ⁱ) + ½⟨P₀x, x⟩`, where `𝒥^P_i` is the compensated cost
of p.17 (with three abbreviations corrected, see `NPRate`).

**Formalization Note** Stated for every profile of square-integrable `L²_𝓕` controls, in particular
for `(uⁱ, ū⁻ⁱ)` with `uⁱ ∈ 𝒰ⁱ_c`, and every `P ∈ Υ` (the paper uses the relaxed compensator). -/
theorem lemma_5_5 {n m d N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (c : Coeffs n m d) (h1 : H1 c)
    (h2 : H2 c) (Sp : Space N d Ω) (P Pdot : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (hP : IsUpsilon c P Pdot) (u : Fin N → ℝ≥0 → Ω → Fin m → ℝ) (hu : ∀ j, IsCtrl Sp c.T (u j))
    (x y : Fin N → ℝ≥0 → Ω → Fin n → ℝ) (hxy : IsNState c Sp u x y) (i : Fin N) :
    NCost c Sp.P x u i = NCostP c P Pdot Sp.P x u i + (1 / 2) * ((P 0 *ᵥ c.x) ⬝ᵥ c.x) := by sorry

end IndefPOMFG
