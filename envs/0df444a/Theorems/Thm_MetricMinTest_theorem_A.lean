-- Prove2me | Theorems.Thm_MetricMinTest_theorem_A
-- name    : MetricMinTest.theorem_A
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:13:16.700592+00:00
-- url     : https://prove2.me/theorems/5f1e5017-ec01-4ff4-a013-6c09f1591127
-- title:
--   Theorem A, p.2 — on the critical ultrametric $d_m$, nonadaptive testers pay $\Theta(F+HL)$ while two rounds pay $O(H[L+\ln(1+m)])$
-- statement:
--   For every $m\ge1$ and $\gamma\in(0,1/4]$ consider the ultrametric $d_m(x,y)=\gamma(1-2^{-\mathrm{lev}(x,y)})$ on $k=4^m$ points, with $H=H_{d_m}(\gamma)$, $F=F_{d_m}(\gamma)$ and $L=\ln(1/\delta)$.
--   1. $d_m$ is an ultrametric and
--   $$H=\frac k{\gamma^2(1+3m/4)},\qquad F=\frac k{\gamma^2}.$$
--   2. Its balls are laminar, and the fractional and integral cover optima agree.
--   3. There are absolute constants $c,C>0$ such that for all $m\ge1$, $\gamma\in(0,1/4]$, $\delta\in(0,1/10]$:
--   $$c(F+HL)\le C^{\mathrm{na}}_{d_m}(\gamma,\delta)\le B^{\mathrm{na}}_{d_m}(\gamma,\delta)\le C(F+HL).$$
--   4. Two rounds suffice: there is an absolute constant $C$ such that for all $\delta\in(0,1/4]$ the optimal positive-instance expected cost of two-round testers is at most $CH[L+\ln(1+m)]$ and their optimal deterministic budget is at most $CHL[1+\ln(1+m)]$.
--   5. At each fixed confidence $\delta\in(0,1/10]$, both the certificate workload $F$ and the nonadaptive cost $C^{\mathrm{na}}_{d_m}$ (hence $B^{\mathrm{na}}_{d_m}$) exceed the optimal two-round cost, expected and budget, by a factor $\Omega(\log k/\log\log k)$.
--
--   All testers may randomize privately and observations may follow arbitrary laws on $[-1,1]$.
--
--   **Formalization Note** The costs are infima over valid testers in $[0,\infty]$; the $\asymp$, $O$ and $\Omega$ statements are written with explicit quantified constants.
--
--   Differences from the source:
--   - encoding: "there is an ultrametric $d_m$" → the explicit $d_m=d_{4,1/2,m}$ of §4.1 on $\mathrm{Fin}\,m\to\mathrm{Fin}\,4$; reason: the paper's construction, which the existential refers to
--   - generalization: "its balls are laminar" (the eligible balls of (2.1)) → any two closed balls $B(j,\rho)$, $B(j',\rho')$ with arbitrary real radii are disjoint or nested; reason: covers the eligible balls
--   - encoding: $C^{\mathrm{na}}\asymp B^{\mathrm{na}}\asymp F+HL$ → $c(F+HL)\le C^{\mathrm{na}}\le B^{\mathrm{na}}\le C(F+HL)$ with absolute $c,C$ chosen before $m,\gamma,\delta$; reason: the paper's convention that $\asymp$ constants are absolute (p.6)
--   - reading: "Two rounds suffice for … $O(H[L+\ln(1+m)])$ … $O(HL[1+\ln(1+m)])$" → for the standing $\delta\in(0,1/4]$, with an absolute constant, for the optimal two-round expected cost $C^{(2)}$ and budget $B^{(2)}$; reason: "For $\delta\le1/10$" belongs to the preceding sentence; this is the stronger reading, which Proposition C.7 gives
--   - reading: "at constant confidence … exceed an achievable two-round cost by a factor $\Omega(\log k/\log\log k)$" → for each $\delta\in(0,1/10]$ some $c>0$ with $c\frac{\ln k}{\ln\ln k}B^{(2)}\le F$, $\le C^{\mathrm{na}}$, and the same for $C^{(2)}$, with $B^{\mathrm{na}}$ following from $C^{\mathrm{na}}\le B^{\mathrm{na}}$ in clause 3; reason: constant confidence = fixed $\delta$; the optimal two-round cost is at most any achievable one, and the budget form is the stronger
--   - encoding: the minima $H_d(\gamma)$ of (1.1) and $F_d(\gamma)$ of (2.1) over indexed balls $B_{j\ell}$ → real infima of the feasible values, with indexed balls encoded by the pairs $(j,i)$ with $d(j,i)<\gamma$; reason: the minima are attained (pp.6–7) and a repeated distance only duplicates a ball at equal cost, so the values are the same
--   - encoding: nonadaptive and two-round testers (Definitions 4.4, C.6), with $C^{\mathrm{na}},B^{\mathrm{na}}$ and two-round costs → valid `RoundTester`s with private randomness $(\Xi,\mu_\xi)$, $\Xi$ in `Type`, in the stack-of-streams model, $\mathbb N$-valued counts for every $\xi$, adaptedness and measurability inside validity, infima in $[0,\infty]$, and two-round budgets over every private draw and every table; reason: Lean model of Definitions 2.1, 4.4 and C.6: a null set with $N(\xi)=\infty$ can be repaired, the page presupposes measurability, an empty class gives $\infty$ so upper bounds are not vacuous, and a query count over every table covers every realization
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem A, p.2

import Mathlib
import Definitions.Def_MetricMinTest_dm
import Definitions.Def_MetricMinTest_IsUltrametric
import Definitions.Def_MetricMinTest_ball
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_certWorkload
import Definitions.Def_MetricMinTest_certWorkloadInt
import Definitions.Def_MetricMinTest_Cna
import Definitions.Def_MetricMinTest_Bna
import Definitions.Def_MetricMinTest_Cround
import Definitions.Def_MetricMinTest_Bround

namespace MetricMinTest

/-- **Theorem A (Joint separation at the critical geometry).** Chen–Fang, *Minimum-Mean Testing
under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem A,
p.2: "For every m ≥ 1 and γ ∈ (0, 1/4], there is an ultrametric d_m on k = 4^m points such that
H = k/(γ²(1 + 3m/4)), F = k/γ². Its balls are laminar and the fractional and integral cover optima
agree. For δ ≤ 1/10, C^na_{d_m}(γ, δ) ≍ B^na_{d_m}(γ, δ) ≍ F + HL. Two rounds suffice for
positive-instance expected cost O(H[L + ln(1 + m)]) and deterministic budget O(HL[1 + ln(1 + m)]).
Thus at constant confidence, both local certificate workload and nonadaptive testing cost exceed
an achievable two-round cost by a factor Ω(log k/ log log k)."

**Formalization Note.** The ultrametric is the explicit `d_m = dm m γ` on `Fin m → Fin 4`
(`k = 4^m`); `H`, `F` are `infoWorkload`, `certWorkload`; `L = ln(1/δ)`. Clauses: (a) ultrametric
and the two workloads; (b) laminar balls `B(j, r)` for all centers and all radii, and integral
optimum = `F`; (c) `≍` with absolute constants (the paper's convention, p.6) as the chain
`c(F + HL) ≤ C^na ≤ B^na ≤ C(F + HL)` for all `δ ∈ (0, 1/10]`; (d) `O` with an absolute
constant, for the optimal two-round expected cost `C^(2)` (sup over positive instances) and
budget `B^(2)`, for the standing `δ ∈ (0, 1/4]`; (e) at each fixed `δ ∈ (0, 1/10]`, a constant
`c > 0` (depending on `δ`) with `F` and `C^na` (hence also `B^na ≥ C^na`) at least
`c · ln k/ln ln k` times the optimal two-round budget and the optimal two-round expected cost. -/
theorem theorem_A :
    (∀ m : ℕ, 1 ≤ m → ∀ γ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      IsUltrametric (dm m γ) ∧
      infoWorkload (dm m γ) γ = (4 : ℝ) ^ m / (γ ^ 2 * (1 + 3 * (m : ℝ) / 4)) ∧
      certWorkload (dm m γ) γ = (4 : ℝ) ^ m / γ ^ 2) ∧
    (∀ m : ℕ, 1 ≤ m → ∀ γ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      (∀ (j j' : Fin m → Fin 4) (ρ ρ' : ℝ),
        Disjoint (ball (dm m γ) j ρ) (ball (dm m γ) j' ρ') ∨
        ball (dm m γ) j ρ ⊆ ball (dm m γ) j' ρ' ∨ ball (dm m γ) j' ρ' ⊆ ball (dm m γ) j ρ) ∧
      certWorkloadInt (dm m γ) γ = certWorkload (dm m γ) γ) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ γ δ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      δ ∈ Set.Ioc (0 : ℝ) (1 / 10) →
      ENNReal.ofReal (c * (certWorkload (dm m γ) γ +
          infoWorkload (dm m γ) γ * Real.log (1 / δ))) ≤ Cna (dm m γ) γ δ ∧
      Cna (dm m γ) γ δ ≤ Bna (dm m γ) γ δ ∧
      Bna (dm m γ) γ δ ≤ ENNReal.ofReal (C * (certWorkload (dm m γ) γ +
          infoWorkload (dm m γ) γ * Real.log (1 / δ)))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ γ δ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      δ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      Cround 2 (dm m γ) γ δ ≤ ENNReal.ofReal (C * infoWorkload (dm m γ) γ *
          (Real.log (1 / δ) + Real.log (1 + m))) ∧
      Bround 2 (dm m γ) γ δ ≤ ENNReal.ofReal (C * infoWorkload (dm m γ) γ * Real.log (1 / δ) *
          (1 + Real.log (1 + m)))) ∧
    (∀ δ : ℝ, δ ∈ Set.Ioc (0 : ℝ) (1 / 10) → ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m → ∀ γ : ℝ,
      γ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      ENNReal.ofReal (c * (Real.log ((4 : ℝ) ^ m) / Real.log (Real.log ((4 : ℝ) ^ m)))) *
          Bround 2 (dm m γ) γ δ ≤ ENNReal.ofReal (certWorkload (dm m γ) γ) ∧
      ENNReal.ofReal (c * (Real.log ((4 : ℝ) ^ m) / Real.log (Real.log ((4 : ℝ) ^ m)))) *
          Bround 2 (dm m γ) γ δ ≤ Cna (dm m γ) γ δ ∧
      ENNReal.ofReal (c * (Real.log ((4 : ℝ) ^ m) / Real.log (Real.log ((4 : ℝ) ^ m)))) *
          Cround 2 (dm m γ) γ δ ≤ ENNReal.ofReal (certWorkload (dm m γ) γ) ∧
      ENNReal.ofReal (c * (Real.log ((4 : ℝ) ^ m) / Real.log (Real.log ((4 : ℝ) ^ m)))) *
          Cround 2 (dm m γ) γ δ ≤ Cna (dm m γ) γ δ) := by sorry

end MetricMinTest
