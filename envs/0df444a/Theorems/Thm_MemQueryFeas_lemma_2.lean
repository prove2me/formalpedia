-- Prove2me | Theorems.Thm_MemQueryFeas_lemma_2
-- name    : MemQueryFeas.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:42:51.592042+00:00
-- url     : https://prove2.me/theorems/b77e3ecf-238a-4569-b21f-2f7088c6a307
-- title:
--   Lemma 2 — most children of a well-behaved phase are well-behaved and satisfy (3.1)
-- statement:
--   In the setting of §3 ($0<\varepsilon\le e^{-d}$, depth $2\le P\le d$, a fixed measurable deterministic $M$-bit learner run against the transform oracle of the skeleton construction): fix $p\in\{2,\dots,P\}$ and a well-behaved layer-$(p-1)$ phase $v\in V_{p-1}$. Then at least half of the $N_p$ children $w=(v\,\|\,i_p)$ of $v$ are well-behaved and additionally satisfy
--   $$
--   I\big(E_w;E_v\mid E^{(<i_p)}_{v,p},\mathrm{Mem}_v,C_v,E_{>p}\big)\le\frac{16M}{N_pN_{p-1}} . \tag{3.1}
--   $$
--
--   This propagates the information constraints from a phase to most of its children; it is the first step of the propagation of the blocking property (Theorem 2).
--
--   Differences from the source:
--   - reading: a majority of the N_p children → at least half: N_p ≤ 2·#(children with the property); reason: the proof obtains at least half (3/4 + 3/4 − 1 = 1/2)
--   - reading: the fixed deterministic learner of §3 (measurability not stated) → its memory update is Borel measurable in the returned normal (DetMemAlg.IsMeasurable); reason: standing convention: Mem_v must be a random variable for the probabilities and information quantities of §3 to be defined
--   - generalization: Algorithm 4, line 5: an arbitrary separation oracle for Q_{E_1,…,E_P} → an arbitrary final oracle (a function of E_1,…,E_P), not required to be valid; reason: phase memories are fixed before the oracle passes its last leaf, so the final oracle never affects them; a valid final oracle is a special case
--   - encoding: the random construction of Algorithm 2 → an abstract probability space carrying E_1,…,E_P and all versions, with their conditional laws as hypotheses (IsSkeleton); reason: same joint law; the paper's probabilities are probabilities under this law
--   - encoding: information in bits (log base 2, p.7) → the nats-valued condMutualInfo compared with ENNReal.ofReal (bits · ln 2); reason: unit conversion; values stay in [0, ∞] (no truncation of ∞)
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Lemma 2, p.12 (PDF p.13), Eq. (3.1); restated p.17

import Mathlib
import Definitions.Def_MemQueryFeas_IsSkeleton
import Definitions.Def_MemQueryFeas_WellBehaved
import Definitions.Def_MemQueryFeas_InfoCond31
import Definitions.Def_MemQueryFeas_DetMemAlg_IsMeasurable

open MeasureTheory

namespace MemQueryFeas

open Classical in
/-- **Lemma 2 (most children of a well-behaved phase are well-behaved and satisfy (3.1)).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026),
Lemma 2, p.12 (PDF p.13): "Fix `p ∈ {2, . . . , P}` and a well-behaved layer-`(p−1)` phase
`v ∈ V_{p−1}`. A majority of child phases `w = (v ∥ i_p)` of `v` are well-behaved and additionally
satisfy `I(E_w; E_v | E^(<i_p)_{v,p}, Mem_v, C_v, E_{>p}) ≤ 16M/(N_pN_{p−1})`. (3.1)"

In the setting of §3 (standing assumptions `0 < ε ≤ e^{−d}`, `2 ≤ P ≤ d`; a fixed measurable
deterministic `M`-bit learner run against the transform oracle of a skeleton model, with any final
oracle): for `p ∈ {2, …, P}` and a well-behaved `v ∈ V_{p−1}`, at least half of the `N_p` children
`v ∥ i` are well-behaved and satisfy (3.1).

**Formalization Note.** "A majority" is read as "at least half" (`N_p ≤ 2·#`), which is what the proof
gives. -/
theorem lemma_2 {d M : ℕ} (ε : ℝ) (hε : 0 < ε) (hεd : ε ≤ Real.exp (-(d : ℝ))) (P : ℕ)
    (hP : 2 ≤ P) (hPd : P ≤ d) (alg : DetMemAlg d M) (halg : alg.IsMeasurable)
    (fin : (ℕ → Op d) → List (Vec d) → Vec d → Option (Vec d)) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure (Op d)) (Eb : ℕ → Ω → Op d)
    (ch : ℕ → List ℕ → ℕ → Ω → Op d) (hS : IsSkeleton d ε P μ ν Eb ch) (p : ℕ) (hp : 2 ≤ p)
    (hpP : p ≤ P) (v : List ℕ) (hv : IsPhase (Np d ε P) (p - 1) v)
    (hwb : WellBehaved ε P alg fin μ Eb ch v) :
    Np d ε P p ≤ 2 * ((Finset.Icc 1 (Np d ε P p)).filter (fun i =>
      WellBehaved ε P alg fin μ Eb ch (v ++ [i]) ∧
        InfoCond31 ε P alg fin μ Eb ch (v ++ [i]))).card := by sorry

end MemQueryFeas
