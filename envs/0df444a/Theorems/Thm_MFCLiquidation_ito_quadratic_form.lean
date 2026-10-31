-- Prove2me | Theorems.Thm_MFCLiquidation_ito_quadratic_form
-- name    : MFCLiquidation.ito_quadratic_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:34.378532+00:00
-- url     : https://prove2.me/theorems/245e0577-1e07-409b-b7f3-b8172a154393
-- title:
--   p.17, Itô's formula [55, Thm 36] for $\mathcal X^\top A\mathcal X$ over $[t,T)$, pathwise
-- statement:
--   Let $S$ be a càdlàg $\mathbb R^n$-valued semimartingale on a probability space, $t<T$, and let $A$ be a symmetric-matrix-valued function on $[0,T]$ with continuous derivative $\dot A$. Then there are processes $I=\int(A_sS_{s-})^\top dS_s$ (left-point Riemann sums), the brackets $[S_i,S_j]$, their continuous parts $[S_i,S_j]^c$ and the Stieltjes integrals $\int A_{ij}\,d[S_i,S_j]^c$, all over $(t,T)$, such that almost surely the jump series converges absolutely and
--   $$S_{T-}^\top A_TS_{T-}=S_t^\top A_tS_t+\int_{(t,T)}2(A_sS_{s-})^\top dS_s+\int_{(t,T)}\operatorname{Tr}(A_s\,d[S,S]^c_s)+\sum_{t<s<T}\big(S_s^\top A_sS_s-S_{s-}^\top A_sS_{s-}-2(A_sS_{s-})^\top\Delta S_s\big)+\int_t^TS_s^\top\dot A_sS_s\,ds .$$
--
--   Taking expectations gives the first display on p.17 for the state $\mathcal X$ (the atoms at $s=t$ of the page's integral and sum combine with $\mathcal X_{t-}^\top A_t\mathcal X_{t-}$ into $\mathcal X_t^\top A_t\mathcal X_t$).
--
--   Differences from the source:
--   - generalization: the expectation identity for the ℝ³-valued state 𝒳 of (2.18) and the solution A of (2.14) → a pathwise almost-sure identity for every càdlàg ℝⁿ-valued semimartingale and every C¹ symmetric matrix function; reason: taking expectations of the pathwise identity, when the terms are integrable as the page presupposes, and specializing n = 3, S = 𝒳, gives the page's display
--   - encoding: ∫_t^{T−} 2(A_s𝒳_{s−})ᵀ d𝒳_s + Σ_{t≤s<T}(…) + ∫ xᵀA_t x μ_{t−}(dx) → S_tᵀA_tS_t plus the integral and the sum over the open interval (t, T); reason: the atoms at s = t telescope: 2(A_t𝒳_{t−})ᵀΔ𝒳_t + (𝒳_tᵀA_t𝒳_t − 𝒳_{t−}ᵀA_t𝒳_{t−} − 2(A_t𝒳_{t−})ᵀΔ𝒳_t) + 𝒳_{t−}ᵀA_t𝒳_{t−} = 𝒳_tᵀA_t𝒳_t
--   - encoding: Tr(A_s d[𝒳, 𝒳]^c_s), [𝒳, 𝒳]^c the continuous part of the bracket → Σ_{i,j} ∫ A_{ij} d[S_i, S_j]^c with [S_i, S_j]^c = [S_i, S_j] − Σ ΔS_iΔS_j (IsContinuousBracket); integrals over (t, T) are integrals of the clipped path; reason: standard definition of the continuous part of the bracket of a semimartingale; Tr(A dQ) = Σᵢⱼ A_ij dQ_ji with Q symmetric
-- source:
--   Fu, Horst & Xia, A Mean-Field Control Problem of Optimal Portfolio Liquidation with Semimartingale Strategies, arXiv:2207.00446v3, proof of Proposition 4.1, p.17, first display ("Using Itô's formula in [55, Theorem 36]")

import Mathlib
import Definitions.Def_KurtzProtter91_Integrals_Skorohod
import Definitions.Def_KurtzProtter91_Integrals_Semimartingale
import Definitions.Def_EthierKurtz_HasCrossVariation
import Definitions.Def_MFCLiquidation_ClippedPath

open MeasureTheory Matrix Set
open scoped NNReal
open KurtzProtter91.Integrals

namespace MFCLiquidation

/-- Itô's formula for the quadratic form `𝒳ᵀA𝒳`, the first display on p.17 of arXiv:2207.00446v3
(citing Protter [55, Theorem 36]), in pathwise form: for a cadlag semimartingale `S` and a `C¹`
symmetric matrix function `A` on `[0, T]`, almost surely

`S_{T−}ᵀA_TS_{T−} = S_tᵀA_tS_t + 2∫_{(t,T)}(A_sS_{s−})ᵀdS_s + ∑ᵢⱼ∫_{(t,T)}Aᵢⱼ d[Sⱼ,Sᵢ]^c_s`
`  + ∑_{t<s<T}(S_sᵀA_sS_s − S_{s−}ᵀA_sS_{s−} − 2(A_sS_{s−})ᵀΔS_s) + ∫_t^T S_sᵀȦ_sS_s ds`.

The page's atoms at `s = t` telescope into the first term on the right, and its expectation form
follows by taking expectations whenever the terms are integrable. -/
theorem ito_quadratic_form {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 m) {n : ℕ} (S : ℝ≥0 → Ω → Fin n → ℝ)
    (hS : IsSemimartingale 𝓕 P S) (t T : ℝ≥0) (ht : t < T)
    (A Adot : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ s ∈ Icc (0 : ℝ) T, (A s).IsSymm)
    (hA : ∀ s ∈ Icc (0 : ℝ) T, ∀ i j,
      HasDerivWithinAt (fun u => A u i j) (Adot s i j) (Icc (0 : ℝ) T) s)
    (hAc : ∀ i j, ContinuousOn (fun u => Adot u i j) (Icc (0 : ℝ) T)) :
    ∃ (I : ℝ≥0 → Ω → Fin 1 → ℝ) (Q Qc Tr : Fin n → Fin n → ℝ≥0 → Ω → ℝ),
      HasStochIntegral (k := 1) (m := n) P
        (fun s ω _ j => (A s *ᵥ clipped t T S s ω) j) (clipped t T S) I ∧
      (∀ i j, EthierKurtz.HasCrossVariation P
        (fun s ω => clipped t T S s ω i) (fun s ω => clipped t T S s ω j) (Q i j)) ∧
      (∀ i j, IsContinuousBracket P
        (fun s ω => clipped t T S s ω i) (fun s ω => clipped t T S s ω j) (Q i j) (Qc i j)) ∧
      (∀ i j, HasStochIntegral (k := 1) (m := 1) P
        (fun s _ _ _ => A s i j) (fun s ω _ => Qc i j s ω) (fun s ω _ => Tr i j s ω)) ∧
      ∀ᵐ ω ∂P,
        let L : ℝ≥0 → Fin n → ℝ := fun u => leftLim (fun v => S v ω) u
        let term : ℝ≥0 → ℝ := fun u =>
          S u ω ⬝ᵥ (A u *ᵥ S u ω) - L u ⬝ᵥ (A u *ᵥ L u) - 2 * ((A u *ᵥ L u) ⬝ᵥ (S u ω - L u))
        Summable (fun u : Ioo t T => term u) ∧
        L T ⬝ᵥ (A T *ᵥ L T) =
          S t ω ⬝ᵥ (A t *ᵥ S t ω) + 2 * I T ω 0 + (∑ i, ∑ j, Tr i j T ω)
            + (∑' u : Ioo t T, term u)
            + ∫ r in (t : ℝ)..(T : ℝ),
                S r.toNNReal ω ⬝ᵥ (Adot r *ᵥ S r.toNNReal ω) := by sorry

end MFCLiquidation
