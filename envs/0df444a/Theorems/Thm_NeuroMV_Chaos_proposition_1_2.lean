-- Prove2me | Theorems.Thm_NeuroMV_Chaos_proposition_1_2
-- name    : NeuroMV.Chaos.proposition_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:36.191335+00:00
-- url     : https://prove2.me/theorems/61b44397-1182-4c4c-a1dc-37f27edc1f5f
-- title:
--   Proposition 1.2, p. 4 — under Hypothesis 1.1 the network equation (1) has a unique strong solution
-- statement:
--   Assume Hypothesis 1.1 ((H1)–(H6)) and the standing assumptions of the network (1): distinct positions in $\Gamma$, $\#\mathcal A_N = N$, nonzero weights $\mathcal S_{\mathcal A_N,\alpha}$, a filtration satisfying the usual conditions, independent Brownian motions $W^r, B^{r,\alpha}$ and Poisson measures $N^r, N^{r,\alpha}$, and initial conditions $z^r\in L^2(\Omega;\mathrm{Càdlàg}([-\tau,0];\mathbb R^d))$ that are $\mathcal F_0$-measurable.
--
--   Then for every network size $N$, every disorder $\omega'\in\Omega'$ and every horizon $T>0$, the network equation (1) has a strong solution $(X^{r,\mathcal A_N}_t)_{r\in\mathcal A_N,\,t\in[-\tau,T]}$, and it is unique: any other strong solution $Y$ satisfies
--   $$\mathbb P\big(Y^{r}_t = X^{r,\mathcal A_N}_t\big)=1\qquad\text{for all } r\in\mathcal A_N,\ t\in[-\tau,T].$$
--
--   The network is a finite system of monotone, path-dependent delay SDEs with jumps; the paper obtains the proposition from its general well-posedness result, Theorem A.2.
--
--   **Formalization Note.** The statement is for every $\omega'$ (the hypotheses hold for every $\omega'$, and the equation is solved $\omega'$ by $\omega'$). Uniqueness is "for each $t$, almost surely", as in the proof of Theorem A.2 (p. 30). The i.i.d. structure of the initial conditions is not needed and not assumed.
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, Proposition 1.2, p. 4, with (1), p. 2, Hypothesis 1.1, pp. 3–4, and Appendix A, p. 21

import Mathlib
import Definitions.Def_NeuroMV_Chaos_Network

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NeuroMV.Chaos

/-- **Proposition 1.2** (p. 4). Under Hypothesis 1.1, for every network size `N`, every disorder
`ω'` and every `T > 0`, the network equation (1) has a strong solution on `[-τ, T]`, and it is
unique: any two strong solutions agree almost surely at every time `t ∈ [-τ, T]`, for every
neuron of `𝒜_N`. -/
theorem proposition_1_2
    {d m n k P : ℕ} {U Ω' Ω : Type*} [MeasurableSpace U] [MeasurableSpace Ω']
    [MeasurableSpace Ω]
    (G : Geometry k P) (ν : Measure U) [SigmaFinite ν] (Pr' : Measure Ω')
    [IsProbabilityMeasure Pr'] (C : Coeffs d m n k P U Ω') (R : Rates Ω')
    (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ)
    (Pr : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℕ → ℝ≥0 → Ω → EthierKurtz.SDEState m) (B : ℕ → Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n)
    (Nall : Ω → Set (ℝ≥0 × ((ℕ × Option (Fin P)) × U))) (z : ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hG : G.Valid) (hH : Hyp11 G ν C R pos 𝒜 S Pr')
    (hnet : NetSetup G ν pos 𝒜 S Pr 𝓕 W B Nall z)
    (N : ℕ) (ω' : Ω') (T : ℝ) (hT : 0 < T) :
    ∃ XN : ℕ → ℝ → Ω → EthierKurtz.SDEState d,
      IsNetSol G ν C pos 𝒜 S Pr 𝓕 W B Nall z N ω' T XN ∧
      ∀ YN : ℕ → ℝ → Ω → EthierKurtz.SDEState d,
        IsNetSol G ν C pos 𝒜 S Pr 𝓕 W B Nall z N ω' T YN →
        ∀ i ∈ 𝒜 N, ∀ t ∈ Set.Icc (-G.τ) T, ∀ᵐ ω ∂Pr, YN i t ω = XN i t ω := by sorry

end NeuroMV.Chaos
