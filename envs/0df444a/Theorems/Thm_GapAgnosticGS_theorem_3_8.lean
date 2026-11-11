-- Prove2me | Theorems.Thm_GapAgnosticGS_theorem_3_8
-- name    : GapAgnosticGS.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:38.387299+00:00
-- url     : https://prove2.me/theorems/977d5a62-d12b-430c-81d8-d2d713053cd8
-- title:
--   Theorem 3.8 — SpecLocate locates the reward gap with $O(\sqrt\Gamma\,\mathrm{polylog})$ expected queries
-- statement:
--   There are absolute constants $C>0$ and $K\in\mathbb N$ with the following property. Let $n\ge2$, let $A$ be an arm register with known $|0\rangle_A$ and reward projector $\Pi$, and let $\delta>0$. There is one algorithm $\mathrm{SpecLocate}(E,\delta)$, built without knowledge of $E$, with classical output $(\mu,\Delta)$, such that for every hidden-basis environment $E$ with a unique best arm $j_\star$:
--
--   1. it terminates almost surely;
--   2. with probability at least $1-\delta$ it returns $\mu\in(0,1)$ and $\Delta\ge\frac3{10}\Delta_{\rm arm}$ with
--   $$\forall j\ne j_\star:\quad p_j\le\mu-\Delta/2<\mu+\Delta/2\le p_\star ;\qquad(2)$$
--   3. its expected number of queries is at most $C\sqrt\Gamma\log^K\frac{n}{\delta\Delta_{\rm arm}}$.
--
--   For a Hamiltonian this locates the spectral gap without any prior gap bound.
--
--   Differences from the source:
--   - reading: SpecLocate(E, δ) (Algorithm 1, built from SpecShrink) → the existence of one algorithm, chosen before E, with every stated property; reason: SpecShrink (Lemma 3.7) is given only existentially, so SpecLocate is as well
--   - reading: O/polylog → absolute C and K chosen before every other quantity; polylog(x) = (log x)^K; reason: the standard meaning
--   - encoding: unique best arm; j ≠ j⋆; terminates almost surely; δ (range unstated) → armGap E > 0; p_j ≠ p⋆; halting probability 1; δ > 0; reason: equivalent under a unique best arm; for δ ≥ 1 the probability clause is trivial
--   - encoding: n arms (range unstated in the statement) → 2 ≤ n; reason: the paper's standing setting (p.2: 'an n-dimensional Hilbert space, where n ≥ 2'), and p_2 and ∆_arm = p⋆ − max_{j≠j⋆} p_j need a second arm; excludes only the case where these are undefined
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 3.8, p.12 (PDF p.13); Algorithm 1, p.12 (PDF p.13); proof in App. A.6, pp.32–33 (PDF pp.33–34)

import Definitions.Def_GapAgnosticGS_HidEnv
import Definitions.Def_GapAgnosticGS_pStar
import Definitions.Def_GapAgnosticGS_armGap
import Definitions.Def_GapAgnosticGS_armComplexity
import Definitions.Def_GapAgnosticGS_OracleAlg_successProb
import Definitions.Def_GapAgnosticGS_OracleAlg_haltProb
import Definitions.Def_GapAgnosticGS_OracleAlg_expQueries

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 3.8, p.12 (PDF p.13): "Given a HidQMAB environment E with unique best arm.
SpecLocate(E, δ) terminates almost surely and with probability at least 1 − δ, returns
µ ∈ (0, 1) and ∆ ≥ (3/10)∆_arm such that ∀j ≠ j⋆: p_j ≤ µ − ∆/2 < µ + ∆/2 ≤ p⋆ (2).
Furthermore, the expected query complexity is O(√Γ polylog(n/(δ∆_arm)))."

There are absolute `C`, `K` such that for every `n ≥ 2`, arm register with known `|0⟩_A` and `Π`,
and `δ > 0`, one algorithm with classical output `(µ, ∆)`, fixed before the environment, satisfies
for every environment with a unique best arm: it halts with probability one; with probability at
least `1 − δ` it halts with `µ ∈ (0,1)`, `∆ ≥ (3/10)∆_arm` and (2); and its expected number of
queries is at most `C √Γ log^K(n/(δ∆_arm))`.

**Formalization Note.** SpecLocate is built from SpecShrink (Lemma 3.7), which the paper gives
only existentially, so the theorem is the existence of an algorithm with every stated property.
"Unique best arm" is `armGap E > 0`; then `j ≠ j⋆` is `p_j ≠ p⋆`. O(·)/polylog are absolute
constants (polylog(x) = (log x)^K). -/
theorem theorem_3_8 :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ (A : Type) [Fintype A] [DecidableEq A] (a₀ : A) (Prj : Matrix A A ℂ)
      (δ : ℝ), 0 < δ →
    ∃ alg : OracleAlg (Fin n × A) (Fin n) (ℝ × ℝ),
      ∀ Env : HidEnv n A a₀ Prj, 0 < armGap Env →
        alg.haltProb Env.E = 1 ∧
        ENNReal.ofReal (1 - δ) ≤ alg.successProb Env.E (fun o _ =>
          o.1 ∈ Set.Ioo 0 1 ∧ 3 / 10 * armGap Env ≤ o.2 ∧
          (∀ j, reward Env j ≠ pStar Env → reward Env j ≤ o.1 - o.2 / 2) ∧
          o.1 - o.2 / 2 < o.1 + o.2 / 2 ∧ o.1 + o.2 / 2 ≤ pStar Env) ∧
        alg.expQueries Env.E ≤ ENNReal.ofReal
          (C * Real.sqrt (armComplexity Env) * Real.log (n / (δ * armGap Env)) ^ K) := by sorry

end GapAgnosticGS
