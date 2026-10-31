-- Prove2me | Theorems.Thm_LiqPremiaEq_theorem_4_5
-- name    : LiqPremiaEq.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:05:46.191642+00:00
-- url     : https://prove2.me/theorems/39439716-1878-4c76-8e5f-c887336ea2f9
-- title:
--   Theorem 4.5 — the explicit Riccati-based tuple (4.11)–(4.14) solves the equilibrium FBSDE, and $\bar S+\mathcal Y-(c\otimes\Lambda)^\top\dot\varphi$ is a Radner equilibrium with transaction costs
-- statement:
--   Consider $N\ge2$ agents with risk aversions $\gamma^n>0$, agent $N$ the most risk-averse, $K\le D$ risky assets with supply $s$, a symmetric positive definite cost matrix $\Lambda$, initial positions with $\sum_n\varphi^n_{0-}=s$, a horizon $T>0$, and a filtered probability space supporting a $D$-dimensional Brownian motion $W$. Suppose Assumption 3.2 (the dividend is $\mathfrak S=\alpha W_T+\beta T$ with $\operatorname{rank}\alpha=\operatorname{rank}\alpha\alpha^\top=K$) and Assumption 4.3 (agent $n<N$ has endowment volatility $\xi^n_t=\xi^nW_t$, $\xi^n\in\mathbb R^{D\times D}$, and agent $N$ has $-\sum_{n<N}\xi^nW_t$).
--
--   Let $(F,H)$ be the solution of the Riccati system (4.8) on $[0,T]$ (Lemma 4.4), let $\Phi$ solve
--
--   $$\Phi'(t)=(I_{N-1}\otimes\Lambda^{-1/2})F^\top(T-t)(I_{N-1}\otimes\Lambda^{-1/2})\Phi(t),\qquad\Phi(0)=I_{K(N-1)},\qquad(4.9)$$
--
--   and let $\Psi(r;t)=(I_{N-1}\otimes\Lambda^{1/2})\Phi(r)\Phi^{-1}(t)(I_{N-1}\otimes\Lambda^{-1/2})$ (4.10). Then:
--
--   1. (4.8) has a solution on $[0,T]$, and for each such solution (4.9) has a solution $\Phi$;
--   2. for all such $F,H,\Phi$, the matrix $\Phi(t)$ is invertible for $t\in[0,T]$, and the tuple $(\varphi,\dot\varphi,\dot Z,\bar S+\mathcal Y-(c\otimes\Lambda)^\top\dot\varphi,\ \bar\sigma-(c\otimes\Lambda)^\top\dot Z)$ given by (4.11)–(4.14), with the frictionless price $\bar S$ and volatility $\bar\sigma=\alpha$ of Proposition 3.3, solves the FBSDE system of Lemma 4.2 (in $\mathbb H^4\times\mathbb H^4\times\mathbb H^2\times\mathcal S^2\times\mathbb H^4$);
--   3. $S=\bar S+\mathcal Y-(c\otimes\Lambda)^\top\dot\varphi$ is a Radner equilibrium with transaction costs: with its drift $\mu$ (that of Lemma 4.2) and volatility $\sigma$ it is a price process with $\mu,\sigma\in\mathbb H^4$, the rates $\dot\varphi^1,\dots,\dot\varphi^{N-1}$ (the blocks of $\dot\varphi$) and $\dot\varphi^N=-\sum_{n<N}\dot\varphi^n$ are optimal for the agents' frictional problems (4.1), and they clear the market.
--
--   No smallness of the costs and no closeness of the risk aversions is assumed: this is the existence of an explicit equilibrium with transaction costs for any number of agents and assets.
--
--   Differences from the source:
--   - reading: “S is a Radner equilibrium with transaction costs” (Definition 3.1 with (4.1)) → IsFrictionalEquilibrium: S is a price process (2.2) with μ ∈ H⁴ and σ ∈ H⁴, the rates are optimal, and the market clears; reason: Section 2 (p.4) requires μ ∈ H⁴(ℝᴷ), σ ∈ H⁴(ℝ^{K×D}) of a price process; this is the printed convention
--   - reading: admissible trading strategies, absolutely continuous with rate φ̇ ∈ H⁴(ℝᴷ) (p.5); footnote 3 says the precise notion is not crucial → the competitors are exactly the rates in H⁴ (progressively measurable on [0, T], E[(∫₀ᵀ‖φ̇_t‖²dt)²] < ∞), positions φ_t = φ_{0−} + ∫₀ᵗ φ̇_u du; reason: the printed notion; no integrability of the objective is added, so the competitor set is not shrunk
--   - reading: Assumption 3.2: β ∈ ℝᴰ → β : Fin K → ℝ; reason: 𝔖 = αW_T + βT ∈ L²(ℝᴷ) (p.4) forces β ∈ ℝᴷ; the printed ℝᴰ does not typecheck when K < D
--   - encoding: “the functions F, H from Lemma 4.4”, “Φ(τ) the solution of (4.9)”, Ψ with Φ⁻¹(t) → ∃ a solution of (4.8) on [0, T]; for every solution ∃ Φ solving (4.9); for every such F, H, Φ: Φ(t) invertible on [0, T] and the conclusions hold; reason: the solutions are unique (Lemma 4.4, linear ODE), so the ∃ ∧ ∀ form is the printed claim; invertibility is presupposed by (4.10) and stated because Lean’s inverse is total
--   - encoding: agent N’s endowment, 𝔖, φ̄₀ and (4.13) → agent N has endowment volatility −∑_{n<N} ξⁿW_t; 𝔖 = αW_T + βT built in; φ̄₀ = ((γ̄/γⁿ)s)ₙ; the matrix integral in (4.13) taken entrywise; reason: zero aggregate endowment (p.3); Assumption 3.2; (7.1) at t = 0 and p.22; the same integral
--   - encoding: Λ^{1/2}, the unique symmetric positive definite square root of Λ (footnote 5), and Λ^{−1/2} → a parameter R with Rᵀ = R, R positive definite and R * R = Λ; Λ^{−1/2} is R⁻¹; reason: the hypotheses determine R uniquely, so R is Λ^{1/2}
--   - encoding: agents n = 1, …, N with N ≥ 2; agent N the most risk-averse (3.2) → agents Fin (M + 1) with 1 ≤ M; agent N is Fin.last M; agents 1, …, N − 1 are Fin M via Fin.castSucc; reason: a relabelling of the same agents
--   - encoding: stacked vectors and matrices in ℝ^{K(N−1)}, ℝ^{K(N−1)×D}, ℝ^{(N−1)D×D}; Kronecker products A ⊗ B, c ⊗ I_K, c ⊗ Λ, 1_{N−1} ⊗ v → index types Fin M × Fin K (resp. Fin M × Fin D), block index first; Mathlib kroneckerMap; c ⊗ B as colKron c B (the Unit column index of a column vector dropped); 1 ⊗ v as onesKron v; reason: the same entries in the same block positions (p.3 convention)
--   - encoding: processes indexed by t ∈ [0, T] → processes indexed by ℝ≥0; progressive measurability is asked of the process stopped at T, time integrals and suprema run over [0, T], and Itô integrands are stopped at T; reason: values after T never enter; every process on [0, T] extends
--   - encoding: a filtered probability space (Ω, 𝓕, (𝓕_t), P) supporting a D-dimensional standard Brownian motion W (p.3) → P a probability measure, 𝓕 an arbitrary filtration, Peng1990.SMP.IsStdBrownian P W and IsBrownianWrt 𝓕 P W (𝓕-adapted, continuous paths, increments W_t − W_s independent of 𝓕_s); reason: the standard definition of a Brownian motion with respect to a filtration; the filtration is not specialized
--   - encoding: Hᵖ and Sᵖ (p.3), Itô dynamics dX = a dt + b dW → IsHp/IsHpMat/IsSp with ℝ≥0∞-valued lower integrals; Sᵖ path continuity required for every ω, as printed; HasItoDynamics through Peng1990.SMP.IsItoIntegral for each entry of b and each Brownian coordinate; reason: the same spaces and the same (Itô) meaning of the differential notation
--   - encoding: terminal conditions φ̇_T = 0, S_T = 𝔖 and market clearing ∑ₙ φⁿ_t = s for all t ∈ [0, T] → terminal conditions almost surely; market clearing almost surely, simultaneously for all t ≤ T; reason: identities between random variables hold almost surely
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Theorem 4.5, p.8 (with Sections 2–4, pp.3–8)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_LiqPremiaEq_IsBrownianWrt
import Definitions.Def_LiqPremiaEq_IsRiccatiSolOn
import Definitions.Def_LiqPremiaEq_phiCoeff
import Definitions.Def_LiqPremiaEq_IsFrictionalEquilibrium
import Definitions.Def_LiqPremiaEq_SolvesFBSDE42
import Definitions.Def_LiqPremiaEq_candPhi

open MeasureTheory Matrix
open scoped NNReal

namespace LiqPremiaEq

/-- **Theorem 4.5.** Let `(F, H)` be the solution of the Riccati system (4.8) on `[0, T]`
(Lemma 4.4), let `Φ` solve
`Φ′(t) = (I_{N−1} ⊗ Λ^{−1/2}) Fᵀ(T − t) (I_{N−1} ⊗ Λ^{−1/2}) Φ(t)`, `Φ(0) = I_{K(N−1)}` (4.9),
and `Ψ(r; t) = (I_{N−1} ⊗ Λ^{1/2}) Φ(r)Φ⁻¹(t) (I_{N−1} ⊗ Λ^{−1/2})` (4.10). Under Assumptions 3.2
(`𝔖 = αW_T + βT`, `rank α = rank αα⊤ = K`) and 4.3 (`ξⁿ_t = ξⁿW_t`), with the frictionless price
`S̄` and volatility `σ̄ = α` of Proposition 3.3, the tuple
`(φ, φ̇, Ż, S̄ + Y − (c ⊗ Λ)ᵀφ̇, σ̄ − (c ⊗ Λ)ᵀŻ)` given by (4.11)–(4.14) solves the FBSDE system of
Lemma 4.2, and `S = S̄ + Y − (c ⊗ Λ)ᵀφ̇` is a Radner equilibrium with transaction costs.

The conclusion states: (1) (4.8) has a solution on `[0, T]`; (2) for every such solution, (4.9) has
a solution `Φ`; (3) for all such `F, H, Φ`, `Φ(t)` is invertible on `[0, T]`, the tuple
(4.11)–(4.14) solves the FBSDE of Lemma 4.2, and `S` with drift `μ` (the drift of Lemma 4.2) and
volatility `σ` is a Radner equilibrium with transaction costs, with trading rates
`φ̇¹, …, φ̇^{N−1}` (the blocks of `φ̇`) and `φ̇ᴺ = −∑_{n<N} φ̇ⁿ`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Theorem 4.5, p.8 (with Sections 2–4, pp.3–8).

**Formalization Note** `N = M + 1 ≥ 2` agents (agent `N = Fin.last M`), `K ≤ D`, `γⁿ > 0` with
(3.2), `Λ` symmetric positive definite with square root `R = Λ^{1/2}` (`Rᵀ = R`, `R ≻ 0`,
`R * R = Λ`, unique), `∑ₙ φⁿ_{0−} = s`, horizon `T > 0`, an arbitrary filtration carrying `W`.
`β ∈ ℝᴷ` (printed `ℝᴰ`). Agent `N`'s endowment volatility is `−∑_{n<N} ξⁿW_t` (zero aggregate
endowment). Uniqueness of `F, H, Φ` makes the "for all solutions" form equivalent to "the"
solutions; invertibility of `Φ(t)` is stated because Lean's inverse is total. -/
theorem theorem_4_5 {Ω : Type*} [mΩ : MeasurableSpace Ω] {M K D : ℕ} (hM : 1 ≤ M)
    (hKD : K ≤ D) (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n) (hγN : ∀ n, γ n ≤ γ (Fin.last M))
    (Λ : Matrix (Fin K) (Fin K) ℝ) (hΛ : Λ.PosDef)
    (R : Matrix (Fin K) (Fin K) ℝ) (hRsymm : Rᵀ = R) (hRpd : R.PosDef) (hRR : R * R = Λ)
    (s : Fin K → ℝ) (φ0m : Fin (M + 1) → Fin K → ℝ) (hφ0 : ∑ n, φ0m n = s)
    (α : Matrix (Fin K) (Fin D) ℝ) (β : Fin K → ℝ) (hα : α.rank = K) (hαα : (α * αᵀ).rank = K)
    (ξ : Fin M → Matrix (Fin D) (Fin D) ℝ) (T : ℝ≥0) (hT : 0 < T)
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → Fin D → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W)
    (hW𝓕 : IsBrownianWrt 𝓕 P W) :
    (∃ F H, IsRiccatiSolOn γ Λ α ξ (Set.Icc 0 (T : ℝ)) F H) ∧
    (∀ F H, IsRiccatiSolOn γ Λ α ξ (Set.Icc 0 (T : ℝ)) F H →
      ∃ Φ, IsLinMatODESol (Set.Icc 0 (T : ℝ)) (fun t => phiCoeff R (F ((T : ℝ) - t))) Φ) ∧
    (∀ F H Φ, IsRiccatiSolOn γ Λ α ξ (Set.Icc 0 (T : ℝ)) F H →
      IsLinMatODESol (Set.Icc 0 (T : ℝ)) (fun t => phiCoeff R (F ((T : ℝ) - t))) Φ →
      (∀ t ∈ Set.Icc 0 (T : ℝ), IsUnit (Φ t).det) ∧
      SolvesFBSDE42 𝓕 P T W γ Λ s (stackInit φ0m) (linEndow ξ W)
        (fun ω => α *ᵥ W T ω + (T : ℝ) • β)
        (candPhi γ Λ R s φ0m H Φ T W) (candPhiDot γ Λ R s φ0m F H Φ T W)
        (fun t _ => candZdot Λ H T t) (candS γ Λ R α β s φ0m F H Φ T W)
        (fun t _ => candSigma γ Λ α H T t) ∧
      IsFrictionalEquilibrium 𝓕 P T W γ Λ s φ0m (linEndow ξ W)
        (fun ω => α *ᵥ W T ω + (T : ℝ) • β)
        (candS γ Λ R α β s φ0m F H Φ T W)
        (fun t ω => priceDrift42 γ s (candSigma γ Λ α H T t)
          (candPhi γ Λ R s φ0m H Φ T W t ω) (stackXi (linEndow ξ W) t ω))
        (fun t _ => candSigma γ Λ α H T t)
        (agentRates (candPhiDot γ Λ R s φ0m F H Φ T W))) := by sorry

end LiqPremiaEq
