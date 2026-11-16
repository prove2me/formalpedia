-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_I_1
-- name    : MetricMinTest.Supplement.theorem_I_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:51:05.732837+00:00
-- url     : https://prove2.me/theorems/3cea399c-b4fd-451d-ac6d-267efa95b6f5
-- title:
--   Theorem I.1, p.30 — cover and packing bounds: cover tester cost $2(L+\gamma)I$, budget $400IL$, $C^\star\le2N_d(r)(L+\gamma-r)/(\gamma-r)^2$, $C^\star\ge\tfrac18M_d(2\gamma)\gamma^{-2}L$
-- statement:
--   Let $d$ be a finite metric or pseudometric, $\gamma,\delta\in(0,1/4]$ and $L=\ln(1/\delta)$. For an integral cover $(j_t,r_t)$, $t=1,\dots,\nu$ (radii $0\le r_t<\gamma$, $\bigcup_tB(j_t,r_t)=[k]$), put $a_t=\gamma-r_t>0$ and $I=\sum_ta_t^{-2}$. The **cover tester** runs, for each $t$, the threshold test at index $j_t$ with threshold $r_t$, gap $a_t$, boundary $L$ and cap $\lceil32a_t^{-2}\ln(\nu/\delta)\rceil$, accepting only if all pass. Then:
--
--   1. the cover tester is valid with positive expected cost at most $2(L+\gamma)I$;
--   2. a truncated amplified version has budget at most $400\,IL$;
--   3. with $N_d(r)$ the minimum number of radius-$r$ balls covering $[k]$ and $M_d(2\gamma)$ the largest number of points with pairwise distances greater than $2\gamma$, for $0\le r<\gamma$,
--   $$C^\star_d(\gamma,\delta)\le\frac{2N_d(r)(L+\gamma-r)}{(\gamma-r)^2},\qquad C^\star_d(\gamma,\delta)\ge\frac18M_d(2\gamma)\gamma^{-2}L .$$
--
--   Covering and packing numbers at scale $\gamma$ thus bracket the adaptive complexity, which yields the doubling-metric bounds of Corollary I.2.
--
--   **Formalization Note** The cover is a list of center–radius pairs and the tests run in list order.
--
--   Differences from the source:
--   - encoding: a finite metric or pseudometric on $[k]$ → a pseudometric on a finite nonempty index type ($k=|\iota|\ge1$); reason: a metric is a pseudometric; $[k]$ has $k\ge1$ points
--   - encoding: integral cover $(j_t,r_t)$ and the cover tester → a list of pairs with $0\le r_t<\gamma$ covering every index, and the deterministic sequential conjunction of the tests in list order; reason: same tester
--   - reading: a truncated amplified version has budget at most $400IL$ → existence of a $(\gamma,\delta)$-valid tester with stopping time at most $400IL$ for every private draw and every table; reason: the claim is the budget achieved by a tester built from the cover (truncation and majority amplification, Lemma A.2)
--   - encoding: the cost measures and testers of §2 (sequential testers with private randomness; $C^\star$, $B^\star$, $C^{\mathrm{na}}$, $B^{\mathrm{na}}$) → the published tester model (stack-of-streams observations, validity including measurability of the acceptance event and the stopping time) and $[0,\infty]$-valued infima, suprema and expectations; reason: same quantities; probabilities and expectations require measurability, and the values can be infinite
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Appendix I and Theorem I.1, p.30

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_Tester_IsValid
import Definitions.Def_MetricMinTest_Supplement_Cstar
import Definitions.Def_MetricMinTest_Supplement_seqTester
import Definitions.Def_MetricMinTest_Supplement_coverNumber
import Definitions.Def_MetricMinTest_Supplement_packingNumber

namespace MetricMinTest.Supplement

open MeasureTheory

/-- **Theorem I.1 (Cover and packing bounds).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Appendix I, p.30: "For an integral cover
(j_t, r_t), t = 1, …, ν, put a_t = γ − r_t > 0 and I = ∑_t a_t⁻². Run threshold tests at boundary L
with caps ⌈32a_t⁻² ln(ν/δ)⌉, accepting only if all pass. Theorem I.1 (Cover and packing bounds).
The cover tester is valid with positive expected cost at most 2(L + γ)I. A truncated amplified
version has budget at most 400IL. If N_d(r) is the minimum number of radius-r balls covering [k],
then for 0 ≤ r < γ, C⋆_d(γ, δ) ≤ 2N_d(r)(L + γ − r)/(γ − r)², C⋆_d(γ, δ) ≥ (1/8) M_d(2γ) γ⁻² L."

**Formalization Note.** Standing setting (§2): `d` a pseudometric on a finite nonempty index type,
`γ, δ ∈ (0, 1/4]`, `L = ln(1/δ)`. An integral cover is a list of balls `(j_t, r_t)` with
`0 ≤ r_t < γ` whose union `⋃ B(j_t, r_t)` is everything. The cover tester is `seqTester` on the
tests `(j_t, r_t, a_t, L, ⌈32 a_t⁻² ln(ν/δ)⌉)` in list order (threshold `r_t`, gap `a_t`), each on
fresh samples. "A truncated amplified version" is stated as the existence of a valid tester with
budget `400 I L` for every private draw and observation table. `N_d(r) = coverNumber`,
`M_d(2γ) = packingNumber d (2γ)` (pairwise distances `> 2γ`). -/
theorem theorem_I_1 {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (hd : IsPseudometric d) (γ δ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4))
    (hδ : δ ∈ Set.Ioc (0 : ℝ) (1 / 4)) (cov : List (ι × ℝ))
    (hcov_r : ∀ q ∈ cov, 0 ≤ q.2 ∧ q.2 < γ) (hcov : ∀ i, ∃ q ∈ cov, d i q.1 ≤ q.2) :
    (seqTester (cov.map (fun q => (q.1, q.2, γ - q.2, Real.log (1 / δ),
        ⌈32 * ((γ - q.2) ^ 2)⁻¹ * Real.log ((cov.length : ℝ) / δ)⌉₊)))).IsValid d γ δ ∧
    (⨆ (P : Instance ι) (_ : IsPositive d γ P),
      ∫⁻ p, (((seqTester (cov.map (fun q => (q.1, q.2, γ - q.2, Real.log (1 / δ),
          ⌈32 * ((γ - q.2) ^ 2)⁻¹ * Real.log ((cov.length : ℝ) / δ)⌉₊)))).stopTime p.1 p.2 : ℕ∞) :
            ENNReal)
        ∂((seqTester (cov.map (fun q => (q.1, q.2, γ - q.2, Real.log (1 / δ),
          ⌈32 * ((γ - q.2) ^ 2)⁻¹ * Real.log ((cov.length : ℝ) / δ)⌉₊)))).μξ.prod
            (streamLaw P))) ≤
      ENNReal.ofReal (2 * (Real.log (1 / δ) + γ) *
        (cov.map (fun q => ((γ - q.2) ^ 2)⁻¹)).sum) ∧
    (∃ T : Tester ι, T.IsValid d γ δ ∧ ∀ ξ ω, ((T.stopTime ξ ω : ℕ∞) : ENNReal) ≤
      ENNReal.ofReal (400 * (cov.map (fun q => ((γ - q.2) ^ 2)⁻¹)).sum * Real.log (1 / δ))) ∧
    (∀ r : ℝ, 0 ≤ r → r < γ →
      Cstar d γ δ ≤ ENNReal.ofReal (2 * (coverNumber d r : ℝ) * (Real.log (1 / δ) + γ - r) /
        (γ - r) ^ 2)) ∧
    ENNReal.ofReal ((packingNumber d (2 * γ) : ℝ) * (γ ^ 2)⁻¹ * Real.log (1 / δ) / 8) ≤
      Cstar d γ δ := by sorry

end MetricMinTest.Supplement
