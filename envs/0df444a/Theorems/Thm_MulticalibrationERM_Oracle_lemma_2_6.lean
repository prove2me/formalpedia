-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_lemma_2_6
-- name    : MulticalibrationERM.Oracle.lemma_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:49:24.023293+00:00
-- url     : https://prove2.me/theorems/c08fb87a-5fc7-4d78-bda3-cd5ee4beee3b
-- title:
--   Lemma 2.6 — uniform concentration for predictable multipliers, both clauses
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $(X_t,Y_t)_{t\le T}$ be independent draws from $D$, adapted to a filtration with $(X_t,Y_t)$ measurable at time $t+1$ and independent of $\mathcal F_t$, and let $\zeta\in(0,1)$. A map $z_t$ is **predictable** if $(\omega,x,y)\mapsto z_t(\omega)(x,y)$ is $\mathcal F_t\otimes\mathcal B$-measurable; $\mathbb E_D[h(X)z_t(X,Y)]$ is the expectation over a fresh example with $z_t$ held fixed.
--
--   (a) For a finite index set $I$ and predictable $z_{t,i}$ into $[-1,1]$, with probability at least $1-\zeta$,
--   $$\sup_{h\in H,\,i\in I}\Big|\sum_{t=1}^T h(X_t)z_{t,i}(X_t,Y_t)-\mathbb E_D[h(X)z_{t,i}(X,Y)]\Big|\le C\sqrt{T\big(d\log(eT)+\log(2|I|/\zeta)\big)}.$$
--   (b) For predictable $z_{t,v}$, $v\in\Lambda$, with $\sum_v|z_{t,v}(x,y)|\le1$, with probability at least $1-\zeta$,
--   $$\sup_{(h_v)\in(H^{\pm})^\Lambda}\Big|\sum_{t=1}^T\sum_{v\in\Lambda}h_v(X_t)z_{t,v}(X_t,Y_t)-\mathbb E_D[h_v(X)z_{t,v}(X,Y)]\Big|\le C\sqrt{T\big(md\log(emT)+\log(1/\zeta)\big)}.$$
--
--   Differences from the source:
--   - encoding: predictable maps with respect to σ-fields F_0 ⊆ F_1 ⊆ … (p. 15) → a filtration ℱ on a probability space; example t is ℱ(t+1)-measurable and independent of ℱ t; z_t jointly ℱ t ⊗ Borel measurable; t = 0, …, T − 1; reason: the paper's definition with an index shift
--   - encoding: (h_v) ∈ (H^±)^Λ, H^± = H ∪ (−H) → a pair (h_v, s_v) ∈ H × Bool at each grid index, contributing pm(s_v)·h_v; reason: every member of H^± is ±h for some h ∈ H
--   - generalization: a class of VC dimension d (standing assumption, p. 12) → any class of VC dimension at most d (with d ≥ 1); reason: every class of VC dimension exactly d is an instance
--   - encoding: auditors h : X → {−1,+1} → h : X → Bool with value pm (h x) ∈ {1, −1} (true ↦ +1); reason: relabelling of the two values; every auditor is an instance
--   - reading: the standard measurability conditions for suprema over H (p. 12) → every auditor measurable and the class pointwise measurable (a countable subclass whose sequences converge pointwise to every member); reason: the paper names no specific condition; pointwise measurability is the standard one under which the suprema are suprema over a countable class
--   - encoding: probability of the failure event → the measure applied to the failure set, i.e. its outer measure when the set is not measurable; reason: equal to the probability when the event is measurable; an outer-measure bound is never weaker
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 15, Lemma 2.6

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_MulticalibrationERM_Oracle_Setting

open MeasureTheory ProbabilityTheory

namespace MulticalibrationERM.Oracle

/-- Lemma 2.6 (p. 15), both clauses: uniform concentration for predictable multipliers.
The examples `E t = (X_t, Y_t)` are i.i.d. `D`, `E t` is measurable for `ℱ (t+1)` and independent
of `ℱ t`; a predictable map `z_t` is `ℱ t`-measurable jointly with its argument. -/
theorem lemma_2_6 :
    ∃ C : ℝ, 0 < C ∧
    ∀ {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ), IsAuditorClass H d →
    ∀ (D : LabeledDist X) {Ω' : Type} [mΩ' : MeasurableSpace Ω'] (P : Measure Ω')
      [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ') (E : ℕ → Ω' → X × ℝ) (T : ℕ),
      (∀ t, Measurable[ℱ (t + 1)] (E t)) →
      (∀ t, Indep (MeasurableSpace.comap (E t) inferInstance) (ℱ t) P) →
      (∀ t, P.map (E t) = D.μ) →
      ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      -- (a) finitely many predictable multipliers into `[−1, 1]`
      (∀ (I : Type) [Fintype I] (z : ℕ → I → Ω' → X × ℝ → ℝ),
        (∀ t i, @Measurable _ _ (MeasurableSpace.prod (ℱ t) inferInstance) _
          (fun p : Ω' × (X × ℝ) => z t i p.1 p.2)) →
        (∀ t i ω e, |z t i ω e| ≤ 1) →
        P {ω | C * Real.sqrt (T * (d * Real.log (Real.exp 1 * T) +
              Real.log (2 * Fintype.card I / ζ))) <
            ⨆ p : H × I, |∑ t ∈ Finset.range T,
              (pm (p.1.1 (E t ω).1) * z t p.2 ω (E t ω) -
                ∫ e, pm (p.1.1 e.1) * z t p.2 ω e ∂D.μ)|} ≤ ENNReal.ofReal ζ) ∧
      -- (b) multipliers indexed by the grid with `∑_v |z_{t,v}| ≤ 1`, auditors `h_v ∈ H±`
      (∀ (K : ℕ), 1 ≤ K → ∀ (z : ℕ → Fin (K + 1) → Ω' → X × ℝ → ℝ),
        (∀ t v, @Measurable _ _ (MeasurableSpace.prod (ℱ t) inferInstance) _
          (fun p : Ω' × (X × ℝ) => z t v p.1 p.2)) →
        (∀ t ω e, ∑ v, |z t v ω e| ≤ 1) →
        P {ω | C * Real.sqrt (T * ((K + 1 : ℝ) * d * Real.log (Real.exp 1 * (K + 1) * T) +
              Real.log (1 / ζ))) <
            ⨆ hs : Fin (K + 1) → H × Bool, |∑ t ∈ Finset.range T, ∑ v,
              (pm (hs v).2 * pm ((hs v).1.1 (E t ω).1) * z t v ω (E t ω) -
                ∫ e, pm (hs v).2 * pm ((hs v).1.1 e.1) * z t v ω e ∂D.μ)|} ≤
          ENNReal.ofReal ζ) := by sorry

end MulticalibrationERM.Oracle
