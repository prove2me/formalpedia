-- Prove2me | Theorems.Thm_LindbladShallow_Supplement_theorem_6_1
-- name    : LindbladShallow.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:25:51.205511+00:00
-- url     : https://prove2.me/theorems/7dc4b31e-1799-40bb-be66-18d0d87d4d80
-- title:
--   Theorem 6.1 — static dissipative hard instances, $d=\Omega_D(\min\{L,\mathcal R_1\})$, $G^{\mathrm{ad}}=\Omega_D(n\min\{L,\theta\})$, $G^{\mathrm{fix}}=\Omega_D(n\min\{L,\mathcal R_{D+1}\})$
-- statement:
--   Fix $D\ge 1$, a wire-dimension bound $q_g\ge 2$ and a gate range $R_g\ge 1$. The system is the cube $[L]^D$, $n=L^D$, with two qubits per site. The generators are the purely dissipative transport instances $\mathcal L=\sum_x\mathcal D_{bS_x}$ of Eq. (51), with $b$ a positive dyadic rational and $\gamma=b^2$. For $\theta\ge1$ evolve for time $T=\theta/\gamma$. A simulator implementing a channel $\mathcal C$ has **half-diamond error** $\tfrac12\|\mathcal C-e^{T\mathcal L}\|_\diamond\le\delta$. Put $E=\log(n/\delta)$.
--
--   **Theorem.** There are absolute constants $c_1,c_2>0$, and for fixed $D,q_g,R_g$ constants $c,\delta_0>0$ and $L_0$, such that for every $L\ge L_0$, $\theta\ge 1$ and $0<\delta<1$ with $\delta\le\delta_0$:
--   1. (48) some transport instance has the property that every simulator in the depth model with half-diamond error at most $\delta$ has depth
--   $$
--   d\ \ge\ c\,\min\{L,\ \mathcal R_1(\theta,E)\};
--   $$
--   2. (49) some transport instance and one input state $\rho$ of the system have the property that every simulator with half-diamond error at most $\delta$ executes, on input $\rho$, an expected number of gates
--   $$
--   G^{\mathrm{adaptive}}\ \ge\ c\,n\,\min\{L,\ \theta\};
--   $$
--   3. (50) some transport instance has the property that every fixed-schedule simulator with half-diamond error at most $\delta$ has a number of gate slots
--   $$
--   G^{\mathrm{fixed}}\ \ge\ c\,n\,\min\{L,\ \mathcal R_{D+1}(\theta,E)\}.
--   $$
--   Each of the three instances has traceless jumps, every site in at most two bonds, and $c_1\gamma\le\lambda\le c_2\gamma$ for the strength parameter $\lambda$ of Section 2.
--
--   The simulators may use arbitrarily many auxiliary registers at arbitrary sites, product initial auxiliary states, arbitrary input-independent shared randomness, arbitrary measurable classical outcome alphabets, single-site instruments for free, and gates on at most two wires of dimension at most $q_g$ at $\ell_\infty$ distance at most $R_g$ (the models of §6.1). The leading volume and time factors match the upper bounds of Theorem 2.1.
--
--   **Formalization Note** The diamond norm `dnorm` is unhalved, so half-diamond error at most $\delta$ is $\mathrm{dnorm}\le 2\delta$. The three instances are chosen after $L,\theta,\delta$ and may differ.
--
--   Differences from the source:
--   - reading: Ω_D(·), "sufficiently large L_side" and δ₀(D, q_g, R_g) → ∃ c > 0, L₀ and δ₀ > 0 depending only on (D, q_g, R_g), chosen before L, θ, δ; reason: the standard reading of the asymptotic statement; implicit constants may depend on D, q_g, R_g (p.51).
--   - reading: λ = Θ(γ) for the hard instances → absolute constants c₁, c₂ > 0 with c₁γ ≤ λ ≤ c₂γ, chosen before everything; reason: the page writes Θ without subscript and the proof gives 8γ ≤ λ < 64γ.
--   - reading: "the lower bound holds for the expected gate count on one input common to every cut" → one system density ρ, chosen after the instance and before every simulator; reason: branch probabilities depend only on the system input's reduced state, so an untouched reference changes no expected count.
--   - reading: gates with at most two input and output wires of dimension ≤ q_g, arbitrary continuous elementary gates → arbitrary instruments on at most two wires of dimension ≤ q_g at sites at ℓ∞ distance ≤ R_g, every other instruction single-site; reason: the page charges "every operation coupling different sites"; a gate with different input and output wires acts on the union of its at most two wires.
--   - encoding: arbitrary classical outcome alphabets and shared input-independent randomness → arbitrary measurable outcome and seed types with probability measures and integrable Kraus densities; reason: this includes finite, countable and continuous alphabets, while explicit integrability excludes only undefined instruments.
--   - reading: classical records travel at most R_g sites per layer → each slot has an anchor site, acts on wires within ℓ∞ distance R_g of it, layers act on disjoint wires, and a slot sees only records of earlier slots with anchors within R_g(t − t′); reason: this is the light-cone condition of §6.1 and Lemma 6.2, up to a constant factor in the speed, which Ω_D absorbs.
--   - reading: one deterministic list of gate locations, disabled slots charged → gate slots on fixed wire sets for all seeds and branches, other slots single-site only, cost = number of gate slots; reason: locations as wires rather than site pairs give the same infimum, since single-site swaps are free in gate count.
--   - encoding: depth maximized over execution branches → the number of layers of the execution bound; reason: trailing layers idle in every branch can be removed without changing the channel, so the infimum over simulators is the same.
--   - encoding: ½‖𝒞 − e^{Tℒ}‖⋄ ≤ δ with 0 < δ < 1 → dnorm(𝒞 − e^{Tℒ}) ≤ 2δ with the hypotheses 0 < δ < 1 and δ ≤ δ₀; reason: dnorm is the unhalved diamond norm; δ < 1 is the page's standing range.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Theorem 6.1, p.51 (pdf p.53); model §6.1, pp.50–51; instances Eq. (51) and λ = Θ(γ), p.52; informal form Theorem B, p.2

import Mathlib
import Definitions.Def_LindbladShallow_gen
import Definitions.Def_LindbladShallow_lam
import Definitions.Def_LindbladShallow_Supplement_transport
import Definitions.Def_LindbladShallow_Supplement_simulator

open scoped Matrix ComplexOrder ENNReal

namespace LindbladShallow

namespace Supplement

/-- **Theorem 6.1** (Static dissipative hard instances; Shen–Wu–Yuan–Zhang, arXiv:2610.05362, held
version sha256 8f4637ef…, p.51, with the model of §6.1, pp.50–51, and the instances of Eq. (51),
p.52). There are absolute constants `c₁, c₂ > 0` and, for fixed `D ≥ 1`, `q_g ≥ 2`, `R_g ≥ 1`,
constants `c, δ₀ > 0` and `L₀` such that for every side `L ≥ L₀`, every `θ ≥ 1` and every
`0 < δ < 1` with `δ ≤ δ₀`, writing `n = L^D` and `E = log(n/δ)`:
* (48) some transport instance (`H = 0`, jumps `J_x = b S_x`) has: every depth-model simulator with
  half-diamond error `½‖𝒞 − e^{Tℒ}‖⋄ ≤ δ`, `T = θ/γ`, `γ = b²`, has depth
  `≥ c · min{L, R₁(θ, E)}`;
* (49) some transport instance and one system input `ρ` have: every simulator with half-diamond
  error `≤ δ` executes on `ρ` an expected number of gates `≥ c · n · min{L, θ}`;
* (50) some transport instance has: every fixed-schedule simulator with half-diamond error `≤ δ`
  has `≥ c · n · min{L, R_{D+1}(θ, E)}` gate slots.
Each of the three instances has traceless jumps, every site in at most two bonds, and
`c₁ γ ≤ λ ≤ c₂ γ` for the strength parameter `λ` of Section 2.

**Formalization Note** `Ω_D(·)` is read as `∃ c > 0` depending only on `(D, q_g, R_g)`,
"sufficiently large `L_side`" as `∃ L₀(D, q_g, R_g)`, and `δ₀ = δ₀(D, q_g, R_g)`; they are chosen
before `L, θ, δ`, and the instance after. The diamond norm `dnorm` is unhalved, so half-diamond
error `≤ δ` is `dnorm ≤ 2δ`. A simulator ranges over every auxiliary layout (any finite type of
registers with positive finite dimensions at any sites of `ℤ^D`), every measurable classical-outcome
alphabet, and arbitrary input-independent shared randomness. The constants in `λ = Θ(γ)` are
absolute (the proof gives `8γ ≤ λ < 64γ`). -/
theorem theorem_6_1 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (D : ℕ) (hD : 1 ≤ D) (qg Rg : ℕ), 2 ≤ qg → 1 ≤ Rg →
    ∃ c δ₀ : ℝ, 0 < c ∧ 0 < δ₀ ∧ ∃ L₀ : ℕ,
    ∀ L : ℕ, L₀ ≤ L → ∀ θ : ℝ, 1 ≤ θ → ∀ δ : ℝ, 0 < δ → δ < 1 → δ ≤ δ₀ →
      let n : ℝ := (L : ℝ) ^ D
      let E : ℝ := Real.log (n / δ)
      (∃ (b : ℚ) (I : Instance (transportParams D hD)), IsTransportInstance L b I ∧
          (∀ e : Fin I.nT, ∀ X ∈ (I.term e).jumpsC, X.trace = 0) ∧
          c₁ * (b : ℝ) ^ 2 ≤ lam I ∧ lam I ≤ c₂ * (b : ℝ) ^ 2 ∧
          ∀ (A : Type) [Fintype A] [DecidableEq A] (site : A → Fin D → ℤ) (dim : A → ℕ)
            (Seed O : Type) [MeasurableSpace Seed] [MeasurableSpace O]
            (S : Simulator I A site dim Seed O), S.Valid qg Rg → S.IsDepthModel Rg →
            dnorm (S.channel - ⇑(supExp (θ / (b : ℝ) ^ 2) (gen I))) ≤ ENNReal.ofReal (2 * δ) →
            c * min (L : ℝ) (radius1 θ E) ≤ (S.nLayers : ℝ)) ∧
      (∃ (b : ℚ) (I : Instance (transportParams D hD)), IsTransportInstance L b I ∧
          (∀ e : Fin I.nT, ∀ X ∈ (I.term e).jumpsC, X.trace = 0) ∧
          c₁ * (b : ℝ) ^ 2 ≤ lam I ∧ lam I ≤ c₂ * (b : ℝ) ^ 2 ∧
          ∃ ρ : Matrix (Sys I) (Sys I) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
          ∀ (A : Type) [Fintype A] [DecidableEq A] (site : A → Fin D → ℤ) (dim : A → ℕ)
            (Seed O : Type) [MeasurableSpace Seed] [MeasurableSpace O]
            (S : Simulator I A site dim Seed O), S.Valid qg Rg →
            dnorm (S.channel - ⇑(supExp (θ / (b : ℝ) ^ 2) (gen I))) ≤ ENNReal.ofReal (2 * δ) →
            c * n * min (L : ℝ) θ ≤ S.expGates ρ) ∧
      (∃ (b : ℚ) (I : Instance (transportParams D hD)), IsTransportInstance L b I ∧
          (∀ e : Fin I.nT, ∀ X ∈ (I.term e).jumpsC, X.trace = 0) ∧
          c₁ * (b : ℝ) ^ 2 ≤ lam I ∧ lam I ≤ c₂ * (b : ℝ) ^ 2 ∧
          ∀ (A : Type) [Fintype A] [DecidableEq A] (site : A → Fin D → ℤ) (dim : A → ℕ)
            (Seed O : Type) [MeasurableSpace Seed] [MeasurableSpace O]
            (S : Simulator I A site dim Seed O) (loc : ℕ → ℕ → Option (Finset (SimWire I A))),
            S.Valid qg Rg → S.RespectsSchedule loc →
            dnorm (S.channel - ⇑(supExp (θ / (b : ℝ) ^ 2) (gen I))) ≤ ENNReal.ofReal (2 * δ) →
            c * n * min (L : ℝ) (radiusD1 D θ E) ≤ (S.scheduleCost loc : ℝ)) := by sorry

end Supplement

end LindbladShallow
