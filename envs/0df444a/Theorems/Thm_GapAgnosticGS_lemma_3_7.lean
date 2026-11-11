-- Prove2me | Theorems.Thm_GapAgnosticGS_lemma_3_7
-- name    : GapAgnosticGS.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:53.887574+00:00
-- url     : https://prove2.me/theorems/2df9485d-f478-4c54-b4d4-8e50880fe9e3
-- title:
--   Lemma 3.7 — SpecShrink shrinks an interval containing $p_k$ to $3/5$ of its width
-- statement:
--   There are absolute constants $C>0$ and $K\in\mathbb N$ with the following property. Let $n\ge2$, let $A$ be an arm register with known $|0\rangle_A$ and reward projector $\Pi$, fix $k\in\{1,2\}$, an interval $I=[u,u+w]\subseteq[0,1]$ with $w>0$, and $\delta>0$. There is one algorithm $\mathrm{SpecShrink}(E,k,I,\delta)$, built without knowledge of $E$, with classical output an interval $J$, such that for every hidden-basis environment $E$ with this $|0\rangle_A$ and $\Pi$ (with $p_k$ the $k$-th largest reward, with multiplicity):
--
--   1. it halts with probability $1$, and every output is an interval $J\subseteq[0,1]$ of width $|J|=\frac35w$;
--   2. if $p_k\in I$, then $\Pr[p_k\in J]\ge1-\delta$;
--   3. every run makes at most $C\,\frac{\sqrt n}{w}\log^K\frac{n}{\delta w}$ queries;
--   4. if the best arm is unique, $w\ge\Delta_{\rm arm}/8$ and $p_k\in I$, the expected number of queries is at most $C\sqrt\Gamma\log^K\frac{n}{\delta\Delta_{\rm arm}}$, where $\Gamma=\sum_{j\ne j_\star}(p_\star-p_j)^{-2}$.
--
--   Repeated shrinking locates the two largest rewards (Theorem 3.8).
--
--   Differences from the source:
--   - reading: If the best arm is unique and w ≥ ∆_arm/8, then expected query complexity is O(√Γ polylog(n/(δ∆_arm))) → the expected-query bound under unique best arm, w ≥ ∆_arm/8 and p_k ∈ I; reason: the proof (App. A.5, p.32) says 'suppose p_k ∈ I and w ≥ ∆_arm/8', and the bound is used only on good attempts (App. A.6)
--   - generalization: when p_k ∈ I returns an interval J ⊆ [0,1] with |J| = (3/5)w → for every environment the algorithm halts with probability 1 and every output is an interval J ⊆ [0,1] of width 3w/5; reason: App. A.5: 'SpecShrink always returns an interval of width 3w/5'; specializes to p_k ∈ I
--   - reading: O/polylog → absolute C and K chosen before every other quantity; polylog(x) = (log x)^K; reason: the standard meaning
--   - reading: for an arbitrary E, the query complexity is O(…) → the worst-case query count (maxQueries) of every run, for every environment; reason: 'for an arbitrary E' with a cap on every run (App. A.5)
--   - encoding: p_k for k ∈ {1, 2}; 'the best arm is unique' → p_1 = p⋆, p_2 = the second largest reward with multiplicity; armGap E > 0; reason: App. A.6's relabelling p_1 > p_2 ≥ ⋯; ∆_arm > 0 iff the best arm is unique
--   - encoding: an interval I ⊆ [0,1] of width w; δ (range unstated) → I = [u, u + w] with 0 ≤ u, u + w ≤ 1, w > 0; δ > 0; reason: the bound √n/w needs w > 0; for δ ≥ 1 the claim is trivial
--   - encoding: n arms (range unstated in the statement) → 2 ≤ n; reason: the paper's standing setting (p.2: 'an n-dimensional Hilbert space, where n ≥ 2'), and p_2 and ∆_arm = p⋆ − max_{j≠j⋆} p_j need a second arm; excludes only the case where these are undefined
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.7 (cf. Lemma 5 in [WYLC21]), p.12 (PDF p.13); proof in App. A.5, pp.31–32 (PDF pp.32–33)

import Definitions.Def_GapAgnosticGS_HidEnv
import Definitions.Def_GapAgnosticGS_pStar
import Definitions.Def_GapAgnosticGS_secondReward
import Definitions.Def_GapAgnosticGS_armGap
import Definitions.Def_GapAgnosticGS_armComplexity
import Definitions.Def_GapAgnosticGS_OracleAlg_successProb
import Definitions.Def_GapAgnosticGS_OracleAlg_haltProb
import Definitions.Def_GapAgnosticGS_OracleAlg_expQueries
import Definitions.Def_GapAgnosticGS_OracleAlg_maxQueries

namespace GapAgnosticGS

open scoped ENNReal

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.7 (cf. Lemma 5 in [WYLC21]), p.12 (PDF p.13): "Fix k ∈ {1, 2} and an interval
I ⊆ [0, 1] of width w. There is an algorithm SpecShrink(E, k, I, δ) that when p_k ∈ I returns an
interval J ⊆ [0, 1] such that |J| = (3/5)w and Pr[p_k ∈ J] ≥ 1 − δ. For an arbitrary E, the query
complexity is O((√n/w) polylog(n/(δw))). If the best arm is unique and w ≥ ∆_arm/8, then expected
query complexity is O(√Γ polylog(n/(δ∆_arm))), where Γ = Σ_{j≠j⋆} 1/(p⋆ − p_j)²"; proof in
Appendix A.5, pp.31–32 (PDF pp.32–33): "Thus SpecShrink always returns an interval of width 3w/5",
"For the instance-dependent bound, suppose p_k ∈ I and w ≥ ∆_arm/8".

There are absolute `C`, `K` such that for every `n ≥ 2`, arm register `A` with known `|0⟩_A` and
`Π`, `k ∈ {1, 2}`, interval `I = [u, u + w] ⊆ [0, 1]` with `w > 0` and `δ > 0`, one algorithm
(classical output `J = [o.1, o.2]`), fixed before the environment, satisfies for every
environment `E`: it halts with probability one and every output is an interval `J ⊆ [0, 1]` of
width `3w/5`; if `p_k ∈ I` then `Pr[p_k ∈ J] ≥ 1 − δ`; every run makes at most
`C (√n/w) log^K(n/(δw))` queries; and if the best arm is unique, `w ≥ ∆_arm/8` and `p_k ∈ I`, the
expected number of queries is at most `C √Γ log^K(n/(δ∆_arm))`.

**Formalization Note.** `p_k` is the `k`-th largest reward with multiplicity (`p_1 = p⋆`,
`p_2 = secondReward`, as in App. A.6). O(·) and polylog are absolute constants `C`, `K`
(polylog(x) = (log x)^K) chosen before everything else. "The best arm is unique" is
`armGap E > 0`. The algorithm may depend on `n, A, a₀, Π, k, I, δ`, not on `E`. -/
theorem lemma_3_7 :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ (A : Type) [Fintype A] [DecidableEq A] (a₀ : A) (Prj : Matrix A A ℂ)
      (k : ℕ), (k = 1 ∨ k = 2) → ∀ (u w δ : ℝ), 0 < w → 0 ≤ u → u + w ≤ 1 → 0 < δ →
    ∃ alg : OracleAlg (Fin n × A) (Fin n) (ℝ × ℝ),
      ∀ Env : HidEnv n A a₀ Prj,
        let pk : ℝ := if k = 1 then pStar Env else secondReward Env
        (∀ h o, alg.step h = .halt o → alg.branch Env.E h ≠ 0 →
          0 ≤ o.1 ∧ o.2 ≤ 1 ∧ o.2 - o.1 = 3 / 5 * w) ∧
        alg.haltProb Env.E = 1 ∧
        (pk ∈ Set.Icc u (u + w) →
          ENNReal.ofReal (1 - δ) ≤ alg.successProb Env.E (fun o _ => pk ∈ Set.Icc o.1 o.2)) ∧
        ((alg.maxQueries Env.E : ℕ∞) : ℝ≥0∞) ≤
          ENNReal.ofReal (C * (Real.sqrt n / w) * Real.log (n / (δ * w)) ^ K) ∧
        (0 < armGap Env → armGap Env / 8 ≤ w → pk ∈ Set.Icc u (u + w) →
          alg.expQueries Env.E ≤ ENNReal.ofReal
            (C * Real.sqrt (armComplexity Env) * Real.log (n / (δ * armGap Env)) ^ K)) := by sorry

end GapAgnosticGS
