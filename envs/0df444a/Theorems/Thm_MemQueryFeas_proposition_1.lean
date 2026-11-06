-- Prove2me | Theorems.Thm_MemQueryFeas_proposition_1
-- name    : MemQueryFeas.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:42:05.53041+00:00
-- url     : https://prove2.me/theorems/f2a940fa-6a53-414c-9bdd-2201f8c0bdda
-- title:
--   Proposition 1 — the Block property at the first layer
-- statement:
--   There is $d_0$ such that for $d\ge d_0$, in the setting of §3 ($0<\varepsilon\le e^{-d}$, $P\in[d]$, a fixed measurable deterministic $M$-bit learner), and for every $k$ with $4k\le\tilde d$: every layer-1 phase $v\in V_1$ is well-behaved, and $R_v$ is
--   $$
--   \lambda_1\text{-}\mathrm{Block}_k\big(1-(2P)^{-1}\ \big|\ \mathrm{Mem}_v,C_v,E_{>1}\big),\qquad\lambda_1=d^{-1}.
--   $$
--
--   This initializes the induction of Theorem 2: before a layer-1 phase the learner has only seen lower-accuracy versions of $E_1$.
--
--   Differences from the source:
--   - reading: d sufficiently large → ∃ d₀, uniform in all other parameters; reason: the usual meaning of the phrase
--   - reading: the fixed deterministic learner of §3 (measurability not stated) → its memory update is Borel measurable in the returned normal (DetMemAlg.IsMeasurable); reason: standing convention: Mem_v must be a random variable for the probabilities and information quantities of §3 to be defined
--   - generalization: Algorithm 4, line 5: an arbitrary separation oracle for Q_{E_1,…,E_P} → an arbitrary final oracle (a function of E_1,…,E_P), not required to be valid; reason: phase memories are fixed before the oracle passes its last leaf, so the final oracle never affects them; a valid final oracle is a special case
--   - encoding: the random construction of Algorithm 2 → an abstract probability space carrying E_1,…,E_P and all versions, with their conditional laws as hypotheses (IsSkeleton); reason: same joint law; the paper's probabilities are probabilities under this law
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Proposition 1, p.11 (PDF p.12); proof pp.28–29

import Mathlib
import Definitions.Def_MemQueryFeas_IsSkeleton
import Definitions.Def_MemQueryFeas_WellBehaved
import Definitions.Def_MemQueryFeas_PhaseBlock
import Definitions.Def_MemQueryFeas_DetMemAlg_IsMeasurable

open MeasureTheory

namespace MemQueryFeas

/-- **Proposition 1 (the Block property at the first layer).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Proposition 1, p.11 (PDF p.12):
"Let `d ≥ 1` be sufficiently large and `4k ≤ d̃`. For any layer-1 phase `v ∈ V_1`, `v` is well-behaved
and `R_v` is `λ_1-Block_k(1 − (2P)^{−1} | Mem_v, C_v, E_{>1})`."

**Formalization Note.** "`d` sufficiently large" is `∃ d₀`, uniform in the other parameters. The
setting is that of §3: `0 < ε ≤ e^{−d}`, `P ∈ [d]`, a fixed measurable deterministic `M`-bit learner,
a skeleton model and any final oracle. `λ_1 = d^{−1}`. -/
theorem proposition_1 :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-(d : ℝ)) →
      ∀ P : ℕ, 1 ≤ P → P ≤ d → ∀ k : ℕ, 4 * k ≤ dt d P →
      ∀ (M : ℕ) (alg : DetMemAlg d M), alg.IsMeasurable →
      ∀ fin : (ℕ → Op d) → List (Vec d) → Vec d → Option (Vec d),
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ν : Measure (Op d)) (Eb : ℕ → Ω → Op d) (ch : ℕ → List ℕ → ℕ → Ω → Op d),
        IsSkeleton d ε P μ ν Eb ch →
      ∀ v : List ℕ, IsPhase (Np d ε P) 1 v →
        WellBehaved ε P alg fin μ Eb ch v ∧
          PhaseBlock ε P alg fin μ Eb ch k (lam d 1) (1 - 1 / (2 * P)) v := by sorry

end MemQueryFeas
