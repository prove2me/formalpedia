-- Prove2me | Theorems.Thm_MemQueryFeas_proposition_2
-- name    : MemQueryFeas.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:42:18.632193+00:00
-- url     : https://prove2.me/theorems/f8b7bede-be4e-452d-a5dc-afdd1e93d992
-- title:
--   Proposition 2 — reduction of non-propagation to a winning Game 1 strategy
-- statement:
--   For $d$ sufficiently large there is a universal constant $c>0$ such that the following holds, in the setting of §3. Fix $p\in\{2,\dots,P\}$ and parameters $\lambda_p\le\Delta'<\frac18\Delta\le\frac18$. Let $v\in V_{p-1}$ be a well-behaved phase such that $R_v$ is $\Delta$-$\mathrm{Block}_k(q\mid\mathrm{Mem}_v,C_v,E_{>p-1})$, and let $w=(v\,\|\,i_p)$ be a well-behaved child satisfying (3.1). Then either
--   1. $R_w$ is $\Delta'$-$\mathrm{Block}_k(q-1/P\mid\mathrm{Mem}_w,C_w,E_{>p})$, or
--   2. there is a strategy winning Game 1 with probability $\xi\ge(12P\ln(6P))^{-1}$, for dimensions $d,\tilde d,k$, accuracies $\delta^{(\le N)}=\delta_p^{(\le N_p)}/\sqrt{3P}$, index $i=i_p$, parameters $(\beta,\gamma)=(8\Delta',\Delta/\sqrt{2P})$, $\eta=\delta_p^{(i_p-1)}$ and some linear map $T$ with $\kappa(T)\le2/(d\delta_p^{(0)})$, whose message satisfies
--   $$
--   I\big(\mathrm{Message};E^{(i)}\mid E^{(<i)}\big)\le\Big(6P\ln(6P)\Big(\frac{4M}{N_p}\Big(1+\frac{8k}{N_{p-1}}\Big)+5k\Big)+2k\log(6Pk)+2Pk^2\log d\Big)\xi .
--   $$
--
--   If the blocking property fails to pass from a phase to a good child, the learner's memory can be turned into a cheap compression scheme for Game 1, which Proposition 3 forbids for suitable parameters.
--
--   **Formalization Note** In alternative 2 the strategy is exhibited on a probability space realizing Game 1 with $N=N_p$, with an invertible $T$, independent private randomness for encoder and decoder and a standard Borel message space. $\log$ is base 2, $\ln$ natural.
--
--   Differences from the source:
--   - reading: d sufficiently large → ∃ d₀, uniform in all other parameters; reason: the usual meaning of the phrase
--   - reading: "there is a universal constant c > 0" (c does not occur in the statement) → ∃ c > 0 kept as a vacuous existential; reason: the constant is printed but unused in this statement
--   - encoding: there is a strategy to win at Game 1 → ∃ a probability space realizing Game 1 (IsGame1Play) with a measurable encoder/decoder, independent private randomness and a standard Borel message space, winning probability ≥ ξ and the information bound; reason: a strategy's success probability and information depend only on the law, which IsGame1Nature pins down
--   - reading: Game 1, line 3: the decoder uses Message and E^(≤i−1) only → no randomness shared between encoder and decoder; reason: literal text; with shared randomness Proposition 3 fails (one-time pad)
--   - encoding: some linear map T with κ(T) ≤ 2/(dδ_p^(0)) → an invertible T with κ(T) ≤ 2/(dδ_p^(0)); reason: κ is only meaningful for invertible T (Lean's quotient is 0 for singular T)
--   - reading: the fixed deterministic learner of §3 (measurability not stated) → its memory update is Borel measurable in the returned normal (DetMemAlg.IsMeasurable); reason: standing convention: Mem_v must be a random variable for the probabilities and information quantities of §3 to be defined
--   - generalization: Algorithm 4, line 5: an arbitrary separation oracle for Q_{E_1,…,E_P} → an arbitrary final oracle (a function of E_1,…,E_P), not required to be valid; reason: phase memories are fixed before the oracle passes its last leaf, so the final oracle never affects them; a valid final oracle is a special case
--   - encoding: the random construction of Algorithm 2 → an abstract probability space carrying E_1,…,E_P and all versions, with their conditional laws as hypotheses (IsSkeleton); reason: same joint law; the paper's probabilities are probabilities under this law
--   - encoding: information in bits (log base 2, p.7) → the nats-valued condMutualInfo compared with ENNReal.ofReal (bits · ln 2); reason: unit conversion; values stay in [0, ∞] (no truncation of ∞)
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Proposition 2, p.13 (PDF p.14); proof §4.3, pp.17–24

import Mathlib
import Definitions.Def_MemQueryFeas_IsSkeleton
import Definitions.Def_MemQueryFeas_WellBehaved
import Definitions.Def_MemQueryFeas_InfoCond31
import Definitions.Def_MemQueryFeas_PhaseBlock
import Definitions.Def_MemQueryFeas_DetMemAlg_IsMeasurable
import Definitions.Def_MemQueryFeas_IsGame1Play
import Definitions.Def_MemQueryFeas_game1Win
import Definitions.Def_MemQueryFeas_game1Output
import Definitions.Def_MemQueryFeas_condNum

open MeasureTheory

namespace MemQueryFeas

/-- **Proposition 2 (reduction to Game 1).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Proposition 2, p.13 (PDF p.14): "For `d`
sufficiently large, there is a universal constant `c > 0` such that the following holds. Fix
`p ∈ {2, . . . , P}`, some parameters `λ_p ≤ ∆′ < (1/8)∆ ≤ 1/8`. Fix a well-behaved layer-`(p − 1)` phase
`v ∈ V_{p−1}` such that `R_v` is `∆-Block_k(q | Mem_v, C_v, E_{>p−1})`. Let `w = (v ∥ i_p)` be a
well-behaved child phase satisfying Eq. (3.1). Then, either 1. `R_w` is
`∆′-Block_k(q − 1/P | Mem_w, C_w, E_{>p})`, 2. or there is a strategy to win at Game 1 with some
probability `ξ ≥ (12P ln(6P))^{−1}`, for dimensions `d, d̃, k`, accuracies `δ^(≤N) := δ_p^(≤N)/√(3P)`,
index `i := i_p`, parameters `(β, γ) := (8∆′, ∆/√(2P))`, `η = δ_p^(i_p−1)`, and some linear map `T` with
`κ(T) ≤ 2/(dδ_p^(0))`, such that the message satisfies the information constraint
`I(Message; E^(i) | E^(<i)) ≤ (6P ln(6P)(4M/N_p (1 + 8k/N_{p−1}) + 5k) + 2k log(6Pk) + 2Pk² log d) ξ`."

In the second alternative, the strategy is exhibited on a realization of Game 1 (`IsGame1Play`) with
`N = N_p`: an invertible `T` with `κ(T) ≤ 2/(dδ_p^(0))`, private encoder/decoder randomness, a standard
Borel message space, winning probability at least `ξ`, and the information bound above in bits.

**Formalization Note.** "`d` sufficiently large" is `∃ d₀`; the universal `c > 0` is printed but does
not occur in the statement and is kept as an existential. The setting is that of §3 (standing
assumptions, a fixed measurable deterministic learner, a skeleton model, any final oracle). The
Game 1 decoder shares no randomness with the encoder. Information is in bits:
`I ≤ X` bits is `condMutualInfo ≤ ENNReal.ofReal (X · ln 2)`. log is base 2, ln natural. -/
theorem proposition_2 :
    ∃ d₀ : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, d₀ ≤ d →
      ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-(d : ℝ)) → ∀ P : ℕ, 2 ≤ P → P ≤ d →
      ∀ (M : ℕ) (alg : DetMemAlg d M), alg.IsMeasurable →
      ∀ fin : (ℕ → Op d) → List (Vec d) → Vec d → Option (Vec d),
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ν : Measure (Op d)) (Eb : ℕ → Ω → Op d) (ch : ℕ → List ℕ → ℕ → Ω → Op d),
        IsSkeleton d ε P μ ν Eb ch →
      ∀ (k p : ℕ) (Δ Δ' q : ℝ), 2 ≤ p → p ≤ P → lam d p ≤ Δ' → Δ' < Δ / 8 → Δ / 8 ≤ 1 / 8 →
      ∀ v : List ℕ, IsPhase (Np d ε P) (p - 1) v →
        WellBehaved ε P alg fin μ Eb ch v → PhaseBlock ε P alg fin μ Eb ch k Δ q v →
      ∀ i : ℕ, 1 ≤ i → i ≤ Np d ε P p →
        WellBehaved ε P alg fin μ Eb ch (v ++ [i]) → InfoCond31 ε P alg fin μ Eb ch (v ++ [i]) →
        PhaseBlock ε P alg fin μ Eb ch k Δ' (q - 1 / P) (v ++ [i]) ∨
        ∃ ξ : ℝ, (12 * P * Real.log (6 * P))⁻¹ ≤ ξ ∧
        ∃ T : Op d, IsUnit T ∧ condNum T ≤ 2 / (d * delta d ε P p 0) ∧
        ∃ (Ω' A B Mes : Type) (_ : MeasurableSpace Ω') (_ : MeasurableSpace A)
          (_ : MeasurableSpace B) (_ : MeasurableSpace Mes) (_ : StandardBorelSpace Mes)
          (_ : Nonempty Mes) (μ' : Measure Ω') (_ : IsProbabilityMeasure μ')
          (ν' : Measure (Op d)) (E' : Ω' → Op d) (ch' : ℕ → Ω' → Op d) (Uenc : Ω' → A)
          (Udec : Ω' → B) (enc : (ℕ → Op d) × A → Mes)
          (dec : Mes × (ℕ → Op d) × B → (Fin k → Vec d)),
          IsGame1Play μ' ν' (dt d P) T (fun j => delta d ε P p j / Real.sqrt (3 * P))
              (Np d ε P p) E' ch' Uenc Udec enc dec ∧
            ENNReal.ofReal ξ ≤ μ' {ω | game1Win (8 * Δ') (Δ / Real.sqrt (2 * P))
              (delta d ε P p (i - 1)) i (fun j => ch' j ω)
              (game1Output enc dec i ch' Uenc Udec ω)} ∧
            ThompsonTutorial.InfoRatio.condMutualInfo μ' (game1Message enc i ch' Uenc) (ch' i)
                (fun ω => truncSeq i (fun j => ch' j ω)) ≤
              ENNReal.ofReal
                ((6 * P * Real.log (6 * P) * (4 * M / Np d ε P p *
                    (1 + 8 * k / Np d ε P (p - 1)) + 5 * k) +
                  2 * k * Real.logb 2 (6 * P * k) + 2 * P * (k : ℝ) ^ 2 * Real.logb 2 d) *
                  ξ * Real.log 2) := by sorry

end MemQueryFeas
