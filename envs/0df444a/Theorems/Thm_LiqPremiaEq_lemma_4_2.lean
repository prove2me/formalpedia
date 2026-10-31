-- Prove2me | Theorems.Thm_LiqPremiaEq_lemma_4_2
-- name    : LiqPremiaEq.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:48.749987+00:00
-- url     : https://prove2.me/theorems/c66959e4-d20a-4d3b-9da2-774ac541a5e5
-- title:
--   Lemma 4.2 — a solution of the FBSDE system gives optimal, market-clearing trading rates
-- statement:
--   Consider $N\ge2$ agents with risk aversions $\gamma^n>0$, agent $N$ the most risk-averse, $K\le D$ risky assets with supply $s\in\mathbb R^K$, a symmetric positive definite transaction cost matrix $\Lambda$, initial positions $\varphi^n_{0-}$ with $\sum_n\varphi^n_{0-}=s$, endowment volatilities $\xi^n\in\mathbb H^2(\mathbb R^D)$ with $\sum_n\xi^n=0$, a horizon $T>0$ and a terminal dividend $\mathfrak S$, on a filtered probability space supporting a $D$-dimensional Brownian motion $W$.
--
--   Suppose $(\varphi,\dot\varphi,\dot Z,S,\sigma)\in\mathbb H^4\times\mathbb H^4\times\mathbb H^2\times\mathcal S^2\times\mathbb H^4$ solves
--
--   $$d\varphi_t=\dot\varphi_t\,dt,\quad\varphi_0=\varphi_{0-},$$
--   $$d\dot\varphi_t=\Big((\Gamma\otimes\Lambda^{-1}\sigma_t\sigma_t^\top)\varphi_t+(\Gamma\otimes\Lambda^{-1}\sigma_t)\xi_t-\frac{\gamma^N}N\mathbb 1_{N-1}\otimes\Lambda^{-1}\sigma_t\sigma_t^\top s\Big)dt+\dot Z_t\,dW_t,\quad\dot\varphi_T=0,$$
--   $$dS_t=\mu_t\,dt+\sigma_t\,dW_t,\quad\mu_t=\frac{\gamma^N}N\sigma_t\sigma_t^\top s+\frac{\sigma_t}N\sum_{n=1}^{N-1}(\gamma^n-\gamma^N)(\sigma_t^\top\varphi^n_t+\xi^n_t),\quad S_T=\mathfrak S,$$
--
--   and that the drift $\mu$ lies in $\mathbb H^2(\mathbb R^K)$. Then the trading rates $\dot\varphi^1,\dots,\dot\varphi^{N-1}$ and $\dot\varphi^N=-\sum_{n=1}^{N-1}\dot\varphi^n$ are optimal for the frictional problems (4.1) of agents $n=1,\dots,N$ (against every rate in $\mathbb H^4$), and they clear the market: $\sum_{n=1}^N\varphi^n_t=s$ for all $t\in[0,T]$.
--
--   This reduces the existence of a Radner equilibrium with transaction costs to the solvability of a fully coupled FBSDE; Theorem 4.5 solves it under linear terminal dividend and endowments.
--
--   Differences from the source:
--   - reading: S is a price process (2.2), whose drift lies in H⁴ by the standing convention of Section 2 (p.4); the frictional problem is well defined for μ ∈ H² (footnote 6) → the drift μ of the third equation is assumed to lie in H² (hypothesis hμ); reason: the FBSDE spaces do not imply any integrability of μ (σ ∈ H⁴ does not give E∫‖σ‖⁴ < ∞), and without it (4.1) can be undefined; the hypothesis is the paper’s standing one
--   - generalization: μ ∈ H⁴(ℝᴷ) (Section 2) → μ ∈ H²(ℝᴷ); reason: H⁴ ⊂ H² on a probability space, so the printed setting is a special case; footnote 6 says H² suffices
--   - reading: admissible trading strategies, absolutely continuous with rate φ̇ ∈ H⁴(ℝᴷ) (p.5); footnote 3 says the precise notion is not crucial → the competitors are exactly the rates in H⁴ (progressively measurable on [0, T], E[(∫₀ᵀ‖φ̇_t‖²dt)²] < ∞), positions φ_t = φ_{0−} + ∫₀ᵗ φ̇_u du; reason: the printed notion; no integrability of the objective is added, so the competitor set is not shrunk
--   - encoding: aggregate endowment zero (∑ₙ ξⁿ = 0) and 𝔖 ∈ L²(ℝᴷ) → ∑ₙ ξⁿ_t(ω) = 0 for all t, ω; no hypothesis on 𝔖; reason: 𝔖 ∈ L² follows from S ∈ S² and S_T = 𝔖
--   - encoding: agents n = 1, …, N with N ≥ 2; agent N the most risk-averse (3.2) → agents Fin (M + 1) with 1 ≤ M; agent N is Fin.last M; agents 1, …, N − 1 are Fin M via Fin.castSucc; reason: a relabelling of the same agents
--   - encoding: stacked vectors and matrices in ℝ^{K(N−1)}, ℝ^{K(N−1)×D}, ℝ^{(N−1)D×D}; Kronecker products A ⊗ B, c ⊗ I_K, c ⊗ Λ, 1_{N−1} ⊗ v → index types Fin M × Fin K (resp. Fin M × Fin D), block index first; Mathlib kroneckerMap; c ⊗ B as colKron c B (the Unit column index of a column vector dropped); 1 ⊗ v as onesKron v; reason: the same entries in the same block positions (p.3 convention)
--   - encoding: processes indexed by t ∈ [0, T] → processes indexed by ℝ≥0; progressive measurability is asked of the process stopped at T, time integrals and suprema run over [0, T], and Itô integrands are stopped at T; reason: values after T never enter; every process on [0, T] extends
--   - encoding: a filtered probability space (Ω, 𝓕, (𝓕_t), P) supporting a D-dimensional standard Brownian motion W (p.3) → P a probability measure, 𝓕 an arbitrary filtration, Peng1990.SMP.IsStdBrownian P W and IsBrownianWrt 𝓕 P W (𝓕-adapted, continuous paths, increments W_t − W_s independent of 𝓕_s); reason: the standard definition of a Brownian motion with respect to a filtration; the filtration is not specialized
--   - encoding: Hᵖ and Sᵖ (p.3), Itô dynamics dX = a dt + b dW → IsHp/IsHpMat/IsSp with ℝ≥0∞-valued lower integrals; Sᵖ path continuity required for every ω, as printed; HasItoDynamics through Peng1990.SMP.IsItoIntegral for each entry of b and each Brownian coordinate; reason: the same spaces and the same (Itô) meaning of the differential notation
--   - encoding: terminal conditions φ̇_T = 0, S_T = 𝔖 and market clearing ∑ₙ φⁿ_t = s for all t ∈ [0, T] → terminal conditions almost surely; market clearing almost surely, simultaneously for all t ≤ T; reason: identities between random variables hold almost surely
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Lemma 4.2, p.7 (with Sections 2–4, pp.3–6)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_LiqPremiaEq_IsBrownianWrt
import Definitions.Def_LiqPremiaEq_IsHp
import Definitions.Def_LiqPremiaEq_IsOptimalRate
import Definitions.Def_LiqPremiaEq_SolvesFBSDE42

open MeasureTheory Matrix
open scoped NNReal

namespace LiqPremiaEq

/-- **Lemma 4.2.** Suppose `(φ, φ̇, Ż, S, σ) ∈ H⁴(ℝ^{K(N−1)}) × H⁴(ℝ^{K(N−1)}) × H²(ℝ^{K(N−1)×D})
× S²(ℝᴷ) × H⁴(ℝ^{K×D})` solves the FBSDE system
`dφ_t = φ̇_t dt`, `φ_0 = φ_{0−}`,
`dφ̇_t = ((Γ ⊗ Λ⁻¹σ_tσ_tᵀ)φ_t + (Γ ⊗ Λ⁻¹σ_t)ξ_t − (γᴺ/N) 1_{N−1} ⊗ Λ⁻¹σ_tσ_tᵀ s) dt + Ż_t dW_t`,
`φ̇_T = 0`,
`dS_t = ((γᴺ/N)σ_tσ_tᵀ s + (σ_t/N) ∑_{n=1}^{N−1}(γⁿ − γᴺ)(σ_tᵀφⁿ_t + ξⁿ_t)) dt + σ_t dW_t`,
`S_T = 𝔖`,
and that its drift `μ` lies in `H²(ℝᴷ)`. Then the trading rates `φ̇¹, …, φ̇^{N−1}` and
`φ̇ᴺ = −∑_{n=1}^{N−1} φ̇ⁿ` are optimal for the frictional problems (4.1) of agents `n = 1, …, N`
and clear the market.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Lemma 4.2, p.7 (with Sections 2–4, pp.3–6).

**Formalization Note** `N = M + 1 ≥ 2` agents (agent `N = Fin.last M`), `K ≤ D` assets, `γⁿ > 0`
with (3.2), `Λ` symmetric positive definite, initial positions `φⁿ_{0−}` with `∑ₙ φⁿ_{0−} = s`,
endowment volatilities `ξⁿ ∈ H²(ℝᴰ)` with `∑ₙ ξⁿ = 0`, and a filtered probability space with an
arbitrary filtration `𝓕` carrying the `D`-dimensional Brownian motion `W`. The drift hypothesis
`μ ∈ H²` is the paper's standing requirement on the price drift (Section 2, `H⁴`; footnote 6:
`H²` suffices for (4.1)). Optimality is against every `H⁴` rate. -/
theorem lemma_4_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {M K D : ℕ} (hM : 1 ≤ M) (hKD : K ≤ D)
    (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n) (hγN : ∀ n, γ n ≤ γ (Fin.last M))
    (Λ : Matrix (Fin K) (Fin K) ℝ) (hΛ : Λ.PosDef) (s : Fin K → ℝ)
    (φ0m : Fin (M + 1) → Fin K → ℝ) (hφ0 : ∑ n, φ0m n = s) (T : ℝ≥0) (hT : 0 < T)
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → Fin D → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W)
    (hW𝓕 : IsBrownianWrt 𝓕 P W)
    (ξp : Fin (M + 1) → ℝ≥0 → Ω → Fin D → ℝ) (hξ : ∀ n, IsHp 𝓕 P T 2 (ξp n))
    (hξsum : ∀ t ω, ∑ n, ξp n t ω = 0) (𝔖 : Ω → Fin K → ℝ)
    (φ φdot : ℝ≥0 → Ω → Fin M × Fin K → ℝ) (Zdot : ℝ≥0 → Ω → Matrix (Fin M × Fin K) (Fin D) ℝ)
    (S : ℝ≥0 → Ω → Fin K → ℝ) (σ : ℝ≥0 → Ω → Matrix (Fin K) (Fin D) ℝ)
    (hsol : SolvesFBSDE42 𝓕 P T W γ Λ s (stackInit φ0m) ξp 𝔖 φ φdot Zdot S σ)
    (hμ : IsHp 𝓕 P T 2 (fun t ω => priceDrift42 γ s (σ t ω) (φ t ω) (stackXi ξp t ω))) :
    (∀ n, IsOptimalRate 𝓕 P T (γ n) Λ (φ0m n) (ξp n)
        (fun t ω => priceDrift42 γ s (σ t ω) (φ t ω) (stackXi ξp t ω)) σ (agentRates φdot n)) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ T, ∑ n, position (φ0m n) (agentRates φdot n) t ω = s) := by sorry

end LiqPremiaEq
