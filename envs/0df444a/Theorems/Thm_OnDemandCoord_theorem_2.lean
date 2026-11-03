-- Prove2me | Theorems.Thm_OnDemandCoord_theorem_2
-- name    : OnDemandCoord.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:29.350762+00:00
-- url     : https://prove2.me/theorems/9a061790-e131-4c3d-8cd1-649364781bd3
-- title:
--   Theorem 2 (System Coordination; corrected: (16′) in place of (16))
-- statement:
--   **Theorem 2 (System Coordination)**, p. 22. Assume the model of §3 and the standing assumption of §5: $Q^p$ satisfies $p\bar F_i(Q^p_i)=c$ for all $i$ and $\underline\tau<\varphi^p=p\,\mathbb P(X_i>Q^p_i\text{ for some }i)$. Then:
--
--   1. a system optimum exists, i.e. a minimizer $(Q^*,\eta^*)$ of the system cost (5) over $Q\ge0$, $\eta\in\mathbb R$;
--
--   and for every system optimum $(Q^*,\eta^*)$, with $S^*=NG(\eta^*)$ and the parameters (14), $m_i=(p\bar F_i(Q^*_i)-c)/(p\bar F_i(Q^*_i))$:
--
--   2. the linear program (8) at $(Q^*,S^*)$ has an optimal solution $\beta^*$ with every $\beta^*_i>0$;
--   3. some membership fees satisfy (16′) and (17):
--   $$\sum_ir_i\ge C(Q^*,\eta^*)-c\sum_iQ^*_i-p\sum_i(1-m_i)\mathbb E[(X_i-Q^*_i)^+],\qquad r_i\le h^p_i-\big(p(1-m_i)\mathbb E[(X_i-Q^*_i)^+]+cQ^*_i\big);$$
--   4. for every optimal $\beta^*$ of (8) with all $\beta^*_i>0$, every choice of the run data of Algorithm 1, every fee vector $r$ satisfying (16′) and (17), and every $T\ge2$, the contract $(r_i,w^F_i,w^C_i)$ of (11)–(12) with the TFRB policy $\kappa_T$ **coordinates** the system at $(Q^*,\eta^*,\kappa_T)$: $\kappa_T\in\mathcal A$; given $Q^*$, $(\eta^*,\kappa_T)$ maximizes the platform's profit (2) over all $\eta$ and all policies in $\mathcal A$; each firm's $Q^*_i$ minimizes its cost (3) given the others' $Q^*_{-i}$ and $(\eta^*,\kappa_T)$; the platform's profit is nonnegative; and each firm's cost is at most $h^p_i$;
--   5. for the same $\beta^*$ and run data, the expected allocation of each firm tends to its target: $\lim_{T\to\infty}\mathbb E[A_i((X-Q^*)^+,S^*)]=\beta^*_i\,\mathbb E[(X_i-Q^*_i)^+]$.
--
--   This is the main result of §5: fill-rate contracts with membership fees implement the first-best staffing decisions in a decentralized system.
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - correction: fees satisfying (16): Σr_i ≥ C(Q*, η*) − pΣ(1 − m_i)E[(X_i − Q_i*)⁺] → fees satisfying (16′): Σr_i ≥ C(Q*, η*) − cΣQ_i* − pΣ(1 − m_i)E[(X_i − Q_i*)⁺]; reason: (15) on p. 21 drops cΣQ_i* against the display on p. 20; printed (16) implies (16′), so every fee of the printed theorem is covered; with (16) no fee may exist (n = 1, X ~ Exp(1), p = 2, c = 1, G uniform on [0.95, 1.95], N = 10: (16) r ≥ 0.6869, (17) r ≤ 0.25; paper.md item 1)
--   - reading: E[A*_i] = β*_i E[X̂_i] at a 'large' T (Lemma 1, warranted in expectation) → the limit as T → ∞ (clause 5); reason: exactness at finite T fails in the generality of the proof (paper.md item 3)
--   - generalization: T a large number → coordination (clause 4) at every T ≥ 2; reason: the equilibrium and participation clauses use only the no-waste property of κ_T
--   - generalization: N sufficiently large → every N > 0; reason: the coordination argument does not use it
--   - reading: Q*, η* as described in Theorem 1 → every global minimizer of (5), with existence (clause 1); reason: p. 10 defines the system optimum as the minimizer; Theorem 1's formulas need extra hypotheses (paper.md items 2, 4)
--   - encoding: β* an optimal solution of (8), used in (11)–(12) → β* optimal with every β*_i > 0, and the existence of such β* (clause 2); reason: (11)–(12) divide by β*_i
--   - encoding: randomized allocation policy; Algorithm 1's arbitrary first allocation and tie-breaks → Markov kernels; the simulation on ν^{⊗T}; run data quantified over; reason: the paper leaves these open; quantifying over them makes no choice for it
--   - generalization: Theorem 2's statement → adds the existence of fees (clause 3), corrected to (16′); reason: the sentence before Theorem 2 asserts it; with (16) it is false
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), Theorem 2, p. 22; (11)–(12) p. 18, (14) p. 21, (16)–(17) pp. 21–22, Algorithm 1 p. 16, (8) p. 15

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Theorem 2 (System Coordination), with (16′)**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), p. 22. Assume `τl < φ^p`. A system
optimum exists. At every system optimum `(Q*, η*)`, with `S* = N G(η*)` and `m` from (14):

* (8) has an optimal `β` with all `β_i > 0`;
* some fees `r` satisfy (16′) and (17);
* for every optimal `β` with all `β_i > 0` and all run data: every contract `(r, m, β)` with (16′) and
  (17), together with the TFRB policy at any `T ≥ 2`, coordinates the system; and the expected
  allocation of each firm at `(X̂, S*)` tends to `β_i E[X̂_i]` as `T → ∞`.

**Formalization Note.** (16′) corrects (16), which drops `c ∑_i Q_i*`: printed (16) implies (16′), so
each `r` of the printed theorem is covered, and fees under (16) and (17) can fail to exist. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Qp : Fin n → ℝ) (hQp : M.IsPermanentBenchmark Qp) (hφ : M.τl < M.phiP Qp) :
    (∃ (Q : Fin n → ℝ) (η : ℝ), M.IsSystemOptimum Q η) ∧
    ∀ (Qstar : Fin n → ℝ) (ηstar : ℝ), M.IsSystemOptimum Qstar ηstar →
      (∃ β, M.IsOptimalLP Qstar (M.S ηstar) β ∧ ∀ i, 0 < β i) ∧
      (∃ r : Fin n → ℝ, M.FeeLower Qstar ηstar (M.mParam Qstar) r ∧
        ∀ i, M.FeeUpper Qp Qstar (M.mParam Qstar) r i) ∧
      ∀ β, M.IsOptimalLP Qstar (M.S ηstar) β → (∀ i, 0 < β i) →
        ∀ run : RunData n (M.S ηstar),
          (∀ (r : Fin n → ℝ), M.FeeLower Qstar ηstar (M.mParam Qstar) r →
            (∀ i, M.FeeUpper Qp Qstar (M.mParam Qstar) r i) →
            ∀ T : ℕ, 2 ≤ T →
              M.Coordinates ⟨r, M.mParam Qstar, β⟩ Qp Qstar ηstar
                (M.tfrb Qstar (M.S ηstar) β run T)) ∧
          ∀ i, Tendsto
            (fun T : ℕ => M.expAlloc (M.tfrb Qstar (M.S ηstar) β run T) Qstar (M.S ηstar) i)
            atTop (𝓝 (β i * M.mean Qstar i)) := by sorry

end OnDemandCoord
