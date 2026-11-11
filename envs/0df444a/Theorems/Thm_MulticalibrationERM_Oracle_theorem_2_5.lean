-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_theorem_2_5
-- name    : MulticalibrationERM.Oracle.theorem_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:50:13.3773+00:00
-- url     : https://prove2.me/theorems/cce20fa9-687f-40e7-a0ec-00bd93c1b64c
-- title:
--   Theorem 2.5 — high-probability hybrid regret of Gaussian follow-the-perturbed-leader (exact and ξ-approximate oracles)
-- statement:
--   There are absolute constants $C_0>0$ and $C_0'\ge C_0$ such that the following holds. Let $G\subseteq\{-1,+1\}^X$ have VC dimension at most $d_G$, $d_G\ge1$, let $T\ge1$, and run Gaussian follow-the-perturbed-leader (2) with $\gamma=4\sqrt{\log(2T)}$ with a $\xi$-approximate weighted ERM oracle for $G$, $0\le\xi\le1$. For every input distribution $D_X$, every environment (on a filtered probability space, $X_t$ is measurable at time $t+1$, independent of the past $\mathcal F_t$ and has law $D_X$; the feedback $Z_t\in[-1,1]$ is measurable at time $t+1$) and every $\zeta\in(0,1)$, with probability at least $1-\zeta$,
--   $$\sup_{g\in G}\sum_{t=1}^{T}Z_t\big(g(X_t)-\bar h_t(X_t)\big)\le\mathrm{Reg}(T,d_G,\zeta),$$
--   with $\mathrm{Reg}$ built on $C_0$ for an exact oracle ($\xi=0$) and on $C_0'$ for $\xi>0$. Each draw from $\pi_t$, including additional independent draws, is one oracle call (`ftplDraw`).
--
--   Differences from the source:
--   - encoding: an environment as in Definition 2.4 (Z_t a function of X_t, the past and randomness independent of the learner's round-t draw) → an adapted process: X_t is F_{t+1}-measurable, independent of F_t, of law D_X; Z_t is F_{t+1}-measurable with |Z_t| ≤ 1; reason: the regret is measured against the mixed predictions h̄_t, which are functions of the past; the learner's own draw g_t does not enter, and a dependence of Z_t on it has the same joint law as a dependence on an independent copy, so the two classes of environments give the same statement
--   - encoding: one absolute constant C_0, and 'a larger absolute constant' for ξ-approximate oracles → C_0 for ξ = 0 and an absolute C_0' ≥ C_0 for 0 < ξ ≤ 1, both quantified before every instance; reason: the two constants of the two sentences of the theorem
--   - encoding: each draw costs one ERM call → each draw is by definition one oracle answer (ftplDraw); reason: the cost clause holds by construction
--   - encoding: rounds t = 1, …, T → rounds t = 0, …, T − 1 (Finset.range T); reason: index shift
--   - encoding: auditors h : X → {−1,+1} → h : X → Bool with value pm (h x) ∈ {1, −1} (true ↦ +1); reason: relabelling of the two values; every auditor is an instance
--   - reading: the standard measurability conditions for suprema over H (p. 12) → every auditor measurable and the class pointwise measurable (a countable subclass whose sequences converge pointwise to every member); reason: the paper names no specific condition; pointwise measurability is the standard one under which the suprema are suprema over a countable class
--   - encoding: probability of the failure event → the measure applied to the failure set, i.e. its outer measure when the set is not measurable; reason: equal to the probability when the event is measurable; an outer-measure bound is never weaker
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 14, Theorem 2.5

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_ERM

open MeasureTheory ProbabilityTheory

namespace MulticalibrationERM.Oracle

/-- Theorem 2.5 (p. 14), both clauses: high-probability regret of Gaussian
follow-the-perturbed-leader against the mixed predictions `h̄_t`, with an exact oracle (constant
`C₀`) and with a `ξ`-approximate oracle, `ξ ≤ 1` (a larger absolute constant `C₀'`). The
environment is any adapted process: `X_t ∼ D_X` independent of everything before round `t`,
`Z_t ∈ [−1, 1]` measurable with respect to everything up to and including `X_t`. The class is
measurable in the sense of the paper's standing assumption (p. 12). Each draw from `π_t` is one
oracle call by construction (`ftplDraw`). -/
theorem theorem_2_5 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C₀' : ℝ, C₀ ≤ C₀' ∧
    ∀ {X : Type} [MeasurableSpace X] (G : Set (X → Bool)) (dG : ℕ), 1 ≤ dG → VC G ≤ dG →
      (∀ g ∈ G, Measurable g) → PointwiseMeasurableClass G →
    ∀ (T : ℕ), 1 ≤ T →
    ∀ (ξ : ℝ), 0 ≤ ξ → ξ ≤ 1 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (O : ERMOracle X G ξ Ω) (DX : Measure X) [IsProbabilityMeasure DX]
      {Ω' : Type} [mΩ' : MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
      (ℱ : Filtration ℕ mΩ') (Xs : ℕ → Ω' → X) (Zs : ℕ → Ω' → ℝ),
      (∀ t < T, Measurable[ℱ (t + 1)] (Xs t)) →
      (∀ t < T, Indep (MeasurableSpace.comap (Xs t) inferInstance) (ℱ t) P) →
      (∀ t < T, P.map (Xs t) = DX) →
      (∀ t < T, Measurable[ℱ (t + 1)] (Zs t)) →
      (∀ t < T, ∀ ω, |Zs t ω| ≤ 1) →
      ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
        P {ω | (if ξ = 0 then Reg C₀ T dG ζ else Reg C₀' T dG ζ) <
            ⨆ g : G, ∑ t ∈ Finset.range T,
              Zs t ω * (pm (g.1 (Xs t ω)) -
                ftplMixed O ν (ftplScale T) t (fun s : Fin t => Xs s ω)
                  (fun s : Fin t => Zs s ω) (Xs t ω))} ≤ ENNReal.ofReal ζ := by sorry

end MulticalibrationERM.Oracle
