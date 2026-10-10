-- Prove2me | Theorems.Thm_MasterVisc_MKV_lemma_5_11
-- name    : MasterVisc.MKV.lemma_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:33:54.168713+00:00
-- url     : https://prove2.me/theorems/8121792d-2c78-45be-8396-a1fef3c4d5ac
-- title:
--   Lemma 5.11, p. 975 — coupling with an independent Brownian motion: ξ_π is σ(η_π, B̃_{[0,δ]})-measurable and ‖ξ − η‖_{ℙ̃,π} ≤ ‖X − X′‖_{ℙ̄,π} + ε
-- statement:
--   Let $0<t<T$, $\mu,\nu\in\mathcal P_2$, and let $\overline{\mathbb P}\in\mathcal P(\mu,\nu)$ be a coupling of $\mu$ and $\nu$ on $\Omega\times\Omega$, with canonical pair $(X,X')$. For a partition $\pi:0\le s_1<\dots<s_m\le t$ and processes $\xi,\eta$ on a probability space $(\tilde\Omega,\tilde{\mathcal F},\tilde{\mathbb P})$ write $\xi_\pi=(\xi_{s_1},\dots,\xi_{s_m})$ and
--   $$\|\xi-\eta\|_{\tilde{\mathbb P},\pi}=\Big(\mathbb E^{\tilde{\mathbb P}}\Big[\max_{1\le j\le m}|\xi_{s_j}-\eta_{s_j}|^2\Big]\Big)^{1/2}.$$
--   Then for every $\varepsilon>0$, $\delta>0$ and partition $\pi$ there are a probability space $(\tilde\Omega,\tilde{\mathcal F},\tilde{\mathbb P})$, two continuous processes $\xi,\eta$ and a $d$-dimensional Brownian motion $\tilde B$ on it such that:
--   1. $\mathcal L_\xi=\mu$, $\mathcal L_\eta=\nu$, and $\eta$ is independent of $\tilde B$;
--   2. $\xi_\pi$ is measurable with respect to $\sigma(\eta_\pi,\tilde B_{[0,\delta]})$;
--   3. $\|\xi-\eta\|_{\tilde{\mathbb P},\pi}\le\|X-X'\|_{\overline{\mathbb P},\pi}+\varepsilon$.
--
--   The lemma lets a control that depends on finitely many past observations of one law be transported to another law at small cost, which is how $V_0$ is shown to be continuous in $\mu$.
--
--   **Formalization Note.** The maximum in (5.14) is printed as $\max_{1\le j\le n}$; it runs over the $m$ points of $\pi$, and the Lean takes the maximum over $j\in\{1,\dots,m\}$. Both sides of (iii) are computed in $[0,\infty]$. The Brownian motion is defined for all times; $\tilde B_{[0,\delta]}$ is its restriction to $[0,\delta]$.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Lemma 5.11 with the notation (5.14), p. 975

import Mathlib
import Definitions.Def_MasterVisc_MKV_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.MKV

/-- Lemma 5.11, p. 975, with the notation (5.14): given `0 < t < T`, `μ, ν ∈ 𝒫₂`, a coupling
`ℙ̄ ∈ 𝒫(μ, ν)`, `ε, δ > 0` and a partition `0 ≤ s₁ < ⋯ < s_m ≤ t`, there are a probability space,
continuous processes `ξ, η` and a Brownian motion `B̃` with `ℒ_ξ = μ`, `ℒ_η = ν`, `η` independent
of `B̃`, `ξ_π` measurable with respect to `σ(η_π, B̃_{[0,δ]})`, and
`‖ξ − η‖_{ℙ̃,π} ≤ ‖X − X'‖_{ℙ̄,π} + ε`. -/
theorem lemma_5_11 {d : ℕ} {T : ℝ≥0}
    (t : ℝ≥0) (ht₀ : 0 < t) (htT : t < T)
    (μ ν : Measure (MasterVisc.Comparison.Path d T)) (hμ : MasterVisc.Comparison.IsP2 μ) (hν : MasterVisc.Comparison.IsP2 ν)
    (Pbar : Measure (MasterVisc.Comparison.Path d T × MasterVisc.Comparison.Path d T))
    (hPbar : Pbar.map Prod.fst = μ ∧ Pbar.map Prod.snd = ν)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ≥0) (hδ : 0 < δ)
    (m : ℕ) (s : Fin m → ℝ≥0) (hs : StrictMono s) (hst : ∀ j, s j ≤ t) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (ξ η : Ω' → MasterVisc.Comparison.Path d T)
      (B : ℝ≥0 → Ω' → EthierKurtz.SDEState d),
      IsProbabilityMeasure P' ∧ Measurable ξ ∧ Measurable η ∧
      EthierKurtz.IsStandardBrownian P' B ∧
      -- (i)
      P'.map ξ = μ ∧ P'.map η = ν ∧ IndepFun η (fun ω (r : ℝ≥0) => B r ω) P' ∧
      -- (ii)
      Measurable[MeasurableSpace.comap (fun ω (j : Fin m) => MasterVisc.Comparison.evalAt (s j) (η ω)) inferInstance ⊔
          MeasurableSpace.comap (fun ω (r : Set.Icc (0 : ℝ≥0) δ) => B r.1 ω) inferInstance]
        (fun ω (j : Fin m) => MasterVisc.Comparison.evalAt (s j) (ξ ω)) ∧
      -- (iii)
      (∫⁻ ω, ⨆ j, ‖MasterVisc.Comparison.evalAt (s j) (ξ ω) - MasterVisc.Comparison.evalAt (s j) (η ω)‖ₑ ^ 2 ∂P') ^ (1 / 2 : ℝ) ≤
        (∫⁻ x, ⨆ j, ‖MasterVisc.Comparison.evalAt (s j) x.1 - MasterVisc.Comparison.evalAt (s j) x.2‖ₑ ^ 2 ∂Pbar) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal ε := by sorry

end MasterVisc.MKV
