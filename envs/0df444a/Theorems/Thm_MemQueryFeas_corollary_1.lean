-- Prove2me | Theorems.Thm_MemQueryFeas_corollary_1
-- name    : MemQueryFeas.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:41:50.394204+00:00
-- url     : https://prove2.me/theorems/a4668d95-b341-4165-85bc-1f575a112e80
-- title:
--   Corollary 1 — at least $N_1\prod_{p=2}^P(N_p/2)$ leaves have the Block property (corrected: adds $d\ln(1/\epsilon)\le M$ from the proof, and $k\le d$)
-- statement:
--   There is a universal constant $c_0>0$ and a threshold $d_0$ such that the following holds for $d\ge d_0$ and $0<\varepsilon\le e^{-d}$. Let $M$ satisfy $d\ln(1/\varepsilon)\le M$ and
--   $$
--   \frac{M\log^4 d}{d^2\log(1/\varepsilon)}\le c_0 ,
--   $$
--   let the learner be a fixed measurable deterministic $M$-bit algorithm, and take
--   $$
--   P=1+\Big\lceil\Big(\frac{c_0d^2\ln(1/\varepsilon)}{M\log^5 d}\Big)^{1/8}\Big\rceil .
--   $$
--   Then there is $k$ with $1\le k\le d$ such that, in the skeleton construction of depth $P$, at least
--   $$
--   N_1\cdot\prod_{p=2}^P\frac{N_p}{2}
--   $$
--   leaves $\ell\in V_P$ have $R_\ell$ $\lambda_P$-$\mathrm{Block}_k\big((2P)^{-1}\mid\mathrm{Mem}_\ell,C_\ell\big)$.
--
--   Combining Proposition 1 with Theorem 2 layer by layer, exponentially many leaves keep the Block property, which forces the learner to spend queries on them.
--
--   Differences from the source:
--   - reading: d sufficiently large → ∃ d₀, uniform in all other parameters; reason: the usual meaning of the phrase
--   - reading: "for some universal constant c₀ > 0" → ∃ c₀ > 0 chosen first, used both in the hypothesis and in the choice of P; reason: the same c₀ appears in both places
--   - correction: only the upper bound M log⁴d/(d² log(1/ε)) ≤ c₀ on M → also d ln(1/ε) ≤ M, the case δ ≥ 0 of the proof's "d^{1+δ} ln(1/ϵ) = M" (p.29, (4.18)); it implies M ≥ 1, which the formula for P needs; reason: without it the corollary is false. Take M = 1 and ε small enough that the chosen P lies in (d/36, d]. Then d̃ = 0, every T_v = I, and R_ℓ = {‖x‖ ≤ 1, x₁ ≤ −1/2} ∋ −e for every leaf, so W = span(e, …) breaks the Block property everywhere, while N₁∏(N_p/2) > 0
--   - reading: "some k ≥ 1" with W ∈ Gr(k, d) in Definition 2 → 1 ≤ k ≤ d; reason: Gr(k, d) is empty for k > d, so Block_k would hold vacuously and the corollary would be trivial; the proof's k = ⌊d/(72C_bP³log²d)⌋ is ≤ d
--   - reading: "one can select … some k ≥ 1" for the fixed learner of §3 → k chosen after the learner and the final oracle, before the random construction; reason: the learner is fixed throughout §3
--   - reading: the fixed deterministic learner of §3 (measurability not stated) → its memory update is Borel measurable in the returned normal (DetMemAlg.IsMeasurable); reason: standing convention: Mem_v must be a random variable for the probabilities and information quantities of §3 to be defined
--   - generalization: Algorithm 4, line 5: an arbitrary separation oracle for Q_{E_1,…,E_P} → an arbitrary final oracle (a function of E_1,…,E_P), not required to be valid; reason: phase memories are fixed before the oracle passes its last leaf, so the final oracle never affects them; a valid final oracle is a special case
--   - encoding: the random construction of Algorithm 2 → an abstract probability space carrying E_1,…,E_P and all versions, with their conditional laws as hypotheses (IsSkeleton); reason: same joint law; the paper's probabilities are probabilities under this law
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Corollary 1, p.11 (PDF p.12); proof pp.29–30, Eq. (4.18)

import Mathlib
import Definitions.Def_MemQueryFeas_IsSkeleton
import Definitions.Def_MemQueryFeas_PhaseBlock
import Definitions.Def_MemQueryFeas_DetMemAlg_IsMeasurable

open MeasureTheory

namespace MemQueryFeas

open Classical in
/-- **Corollary 1 (many leaves with the Block property; corrected).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Corollary 1, p.11 (PDF p.12): "Let `d ≥ 1` be
sufficiently large and assume `M log⁴ d/(d² log(1/ϵ)) ≤ c_0` for some universal constant `c_0 > 0`.
Then, one can select `P = 1 + ⌈(c_0d² ln(1/ϵ)/(M log⁵ d))^{1/8}⌉` and some `k ≥ 1`, for which there are at
least `N_1 · ∏_{p=2}^P (N_p/2)` layer-`P` phases `ℓ ∈ V_P` such that `R_ℓ` is
`λ_P-Block_k((2P)^{−1} | Mem_ℓ, C_ℓ)`."

**Formalization Note.** `c₀` is a universal constant (existential, chosen first), then `d₀`. The
learner is fixed (measurable, deterministic, `M` bits) before `k` is chosen, as in §3. Leaves are
counted through their lexicographic index (`leafOf`). log is base 2, ln natural.

**Correction.** The printed statement only bounds `M` from above. Its proof (p.29, (4.18)) starts
from "`d^{1+δ} ln(1/ϵ) = M`" with `δ ∈ [0, 1]`, i.e. `d ln(1/ϵ) ≤ M`, and that lower bound is added
here. Without it the printed corollary fails: take `M = 1` and `ϵ` so small that the selected `P`
lies in `(d/36, d]`. Then `d̃ = ⌊d/(36P)⌋ = 0`, all `T_v = I` and
`R_ℓ = {‖x‖ ≤ 1, x₁ ≤ −1/2}` is deterministic and contains `−e`. So `W = span(e, …)` violates the
blocking property at every leaf, while `N₁∏(N_p/2) > 0`. The hypothesis `d ln(1/ϵ) ≤ M` also gives
`M ≥ 1`, which the formula for `P` needs. `k ≤ d` is required because `Block_k` quantifies over
`W ∈ Gr(k, d)`. For `k > d` there is no such `W`, and every region would be blocking vacuously. -/
theorem corollary_1 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-(d : ℝ)) →
      ∀ M : ℕ, (d : ℝ) * Real.log (1 / ε) ≤ M →
        (M : ℝ) * Real.logb 2 d ^ 4 / ((d : ℝ) ^ 2 * Real.logb 2 (1 / ε)) ≤ c₀ →
      ∀ alg : DetMemAlg d M, alg.IsMeasurable →
      ∀ fin : (ℕ → Op d) → List (Vec d) → Vec d → Option (Vec d),
        let P : ℕ := 1 + ⌈(c₀ * (d : ℝ) ^ 2 * Real.log (1 / ε) /
          ((M : ℝ) * Real.logb 2 d ^ 5)) ^ ((1 : ℝ) / 8)⌉₊
        ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ν : Measure (Op d)) (Eb : ℕ → Ω → Op d) (ch : ℕ → List ℕ → ℕ → Ω → Op d),
        IsSkeleton d ε P μ ν Eb ch →
          (Np d ε P 1 : ℝ) * ∏ p ∈ Finset.Icc 2 P, ((Np d ε P p : ℝ) / 2) ≤
            (((Finset.range (numLeaves (Np d ε P) P)).filter (fun n =>
              PhaseBlock ε P alg fin μ Eb ch k (lam d P) (1 / (2 * P))
                (leafOf (Np d ε P) P n))).card : ℝ) := by sorry

end MemQueryFeas
