-- Prove2me | Theorems.Thm_MetricMinTest_theorem_3_1
-- name    : MetricMinTest.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:11:02.405602+00:00
-- url     : https://prove2.me/theorems/69c495fa-1a42-4069-91c7-132a2fa7ed69
-- title:
--   Theorem 3.1, p.7 — information lower bound $\mathbb E_{P^\star}\tau\ge\tfrac12D_\delta H\ge\tfrac18H\ln(1/\delta)$
-- statement:
--   Let $d$ be a pseudometric on a finite index set and $\gamma,\delta\in(0,1/4]$. Let $P^\star$ give every index the signed Bernoulli law of mean $\gamma$. Every $(\gamma,\delta)$-valid sequential tester, with arbitrary private randomization, satisfies
--   $$\mathbb E_{P^\star}\tau\ \ge\ \tfrac12D_\delta H_d(\gamma)\ \ge\ \tfrac18H_d(\gamma)\ln(1/\delta),$$
--   where $D_\delta=\mathrm{kl}(1-\delta,\delta)$.
--
--   The information workload is therefore a lower bound for every tester, adaptive or not, up to the confidence factor.
--
--   **Formalization Note** Testers follow the stack-of-streams model; $\mathbb E_{P^\star}\tau$ is the integral of the stopping time in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: "a tester" → a sequential tester with private randomness $(\Xi,\mu_\xi)$, $\Xi$ in `Type`, in the stack-of-streams observation model, validity including measurability of acceptance and stopping time; reason: Lean model of §2; same testers and laws of transcripts
--   - encoding: $P^\star$ → any instance whose every law is the signed Bernoulli law of mean $\gamma$; reason: Lean convention; same instance
--   - encoding: the minimum $H_d(\gamma)$ of (1.1) → the real infimum of the feasible masses; reason: the feasible set is nonempty and bounded below and the minimum is attained (p.7), so the value is the same
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem 3.1, p.7

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_Tester_IsValid
import Definitions.Def_MetricMinTest_signedBernoulli
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_Ddelta

namespace MetricMinTest

open MeasureTheory

/-- **Theorem 3.1 (Information lower bound).** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem 3.1, p.7: "Let P⋆
give every index signed Bernoulli mean γ. Every valid tester satisfies
E_{P⋆} τ ≥ ½ D_δ H_d(γ) ≥ ⅛ H_d(γ) ln(1/δ)."

**Formalization Note.** Standing assumptions of §2 (p.6): `d` a pseudometric on a finite index
set, `γ, δ ∈ (0, 1/4]`. "Valid tester" is any sequential privately randomized tester
(`Tester.IsValid`). `P⋆` is any instance whose every law is `signedBernoulli γ`. `E_{P⋆} τ` is the
`ℝ≥0∞` integral of the stopping time under `μξ ⊗ streamLaw P⋆`. -/
theorem theorem_3_1 {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (hd : IsPseudometric d) (γ δ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4))
    (hδ : δ ∈ Set.Ioc (0 : ℝ) (1 / 4)) (T : Tester ι) (hT : T.IsValid d γ δ) (P : Instance ι)
    (hP : ∀ i, P.law i = signedBernoulli γ) :
    ENNReal.ofReal (Ddelta δ * infoWorkload d γ / 2) ≤
        ∫⁻ p, ((T.stopTime p.1 p.2 : ℕ∞) : ENNReal) ∂(T.μξ.prod (streamLaw P)) ∧
    infoWorkload d γ * Real.log (1 / δ) / 8 ≤ Ddelta δ * infoWorkload d γ / 2 := by sorry

end MetricMinTest
