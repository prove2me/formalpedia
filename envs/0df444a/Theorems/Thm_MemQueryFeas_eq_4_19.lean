-- Prove2me | Theorems.Thm_MemQueryFeas_eq_4_19
-- name    : MemQueryFeas.eq_4_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:42:04.89324+00:00
-- url     : https://prove2.me/theorems/e3d1aa80-39ef-472f-9206-aaf4d5636848
-- title:
--   Eq. (4.19) — expected number of non-skipped Block leaves is at least $(d\ln(1/\epsilon))^{P/4}$ (corrected: adds $d\ln(1/\epsilon)\le M$ from the proof, and $k\le d$)
-- statement:
--   Under the hypotheses of Corollary 1 (including $d\ln(1/\varepsilon)\le M$), with its choice of $P$ (and some $k$ with $1\le k\le d$), let the learner be a fixed measurable deterministic $M$-bit algorithm and let the final oracle of Algorithm 4 be a valid separation oracle for $Q_{E_1,\dots,E_P}$. Let $U_P$ be the set of leaves $\ell$ for which $R_\ell$ is $\lambda_P$-$\mathrm{Block}_k((2P)^{-1}\mid\mathrm{Mem}_\ell,C_\ell)$, let
--   $$
--   \mathcal E_\ell=\{\text{the oracle reaches leaf }\ell\text{ and }O_\ell(x_{t_\ell})=\mathrm{Success}\},
--   $$
--   where $x_{t_\ell}=\psi_{query}(\mathrm{Mem}_\ell)$, and let $\mathcal E_{bad}$ be the event that the instance is invalid (the complement of the event of Lemma 1). Then
--   $$
--   \mathbb E\Big[\sum_{\ell\in U_P}\mathbf 1\big(\mathcal E_\ell^c\cap\mathcal E_{bad}^c\big)\Big]\ \ge\ \big(d\ln(1/\varepsilon)\big)^{P/4}.
--   $$
--
--   Each such leaf costs the learner a query, so this is the expected query lower bound of the proof of Theorem 1 in the low-memory regime.
--
--   Differences from the source:
--   - reading: d sufficiently large → ∃ d₀, uniform in all other parameters; reason: the usual meaning of the phrase
--   - correction: Corollary 1's hypotheses as printed (only an upper bound on M) → also d ln(1/ε) ≤ M, the case δ ≥ 0 of "d^{1+δ} ln(1/ϵ) = M" under which (4.18) chooses P and k; reason: without it the display is false. For M = 1 and ε small enough that P ∈ (d/36, d], d̃ = 0 and every path oracle answers Success on the cap {‖x‖ ≤ 1, x₁ ≤ −1/2}. A learner whose first query is −e then skips all leaves in round 0, and the left side is 0
--   - reading: U_P, the leaves given by Corollary 1 → the set of all leaves with the Block property for the chosen k, where 1 ≤ k ≤ d; reason: Corollary 1 guarantees at least N_1∏(N_p/2) of them and the proof uses this set; k ≤ d because Block_k quantifies over W ∈ Gr(k, d), which is empty for k > d
--   - reading: E_ℓ: the oracle reaches leaf ℓ and O_ℓ(x_{t_ℓ}) = Success → Mem_ℓ is defined (transient-leaf reading of Definition 1) and O_ℓ(ψ_query(Mem_ℓ)) = Success; reason: only this reading counts the skipped leaves as the proof does (p.30)
--   - encoding: E[Σ_{ℓ∈U_P} 1(·)] → Σ_{ℓ∈U_P} P(·); reason: linearity of expectation over a finite set
--   - reading: the trailing "= (d ln(1/ϵ))^{Ω̃(d^{(1−δ)})}" → not stated; reason: an asymptotic remark (with a typo for (1−δ)/8); the milestone is the displayed inequality
--   - reading: the fixed deterministic learner of §3 (measurability not stated) → its memory update is Borel measurable in the returned normal (DetMemAlg.IsMeasurable); reason: standing convention: Mem_v must be a random variable for the probabilities and information quantities of §3 to be defined
--   - encoding: the random construction of Algorithm 2 → an abstract probability space carrying E_1,…,E_P and all versions, with their conditional laws as hypotheses (IsSkeleton); reason: same joint law; the paper's probabilities are probabilities under this law
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Proof of Theorem 1, p.30 (PDF p.31), Eq. (4.19)

import Mathlib
import Definitions.Def_MemQueryFeas_IsSkeleton
import Definitions.Def_MemQueryFeas_PhaseBlock
import Definitions.Def_MemQueryFeas_GoodEvent
import Definitions.Def_MemQueryFeas_IsValidAdaptive
import Definitions.Def_MemQueryFeas_DetMemAlg_IsMeasurable

open MeasureTheory

namespace MemQueryFeas

open Classical in
/-- **Eq. (4.19) (expected number of non-skipped leaves with the Block property; corrected).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), proof of Theorem 1,
p.30 (PDF p.31), Eq. (4.19): "In expectation, the total number of queries during the run is at least
`E[Σ_{ℓ∈U_P} 1(E_ℓ^c ∩ E_bad^c)] ≥ |U_P|/(4P) ≥ (1/(2P))(ln(1/ϵ)/(8P² log d))^P ≥ (d ln(1/ϵ))^{P/4}`".
Here `U_P` is the set of leaves `ℓ` with `R_ℓ` `λ_P-Block_k(1/(2P) | Mem_ℓ, C_ℓ)`,
`E_ℓ := {The oracle reaches leaf ℓ and O_ℓ(x_{t_ℓ}) = Success}` and `E_bad` is the event that the
instance is invalid (the complement of Lemma 1's event).

Under the hypotheses of Corollary 1 (with `d ln(1/ε) ≤ M`) and its choice of `P` (with some `1 ≤ k ≤ d`): for a measurable
deterministic `M`-bit learner and a final oracle that is valid for `Q_{E_1,…,E_P}`,
`Σ_{ℓ∈U_P} P(E_ℓ^c ∩ E_bad^c) ≥ (d ln(1/ε))^{P/4}`.

**Formalization Note.** `c₀` (existential, universal) and `d₀` are those of this statement. The
leaf `ℓ` is "reached" when `Mem_ℓ` exists (`memV`, transient-leaf reading of Definition 1), and
`x_{t_ℓ} = ψ_query(Mem_ℓ)`. The expectation of the sum of indicators is the sum of the probabilities.
The trailing "`= (d ln(1/ϵ))^{Ω̃(d^{(1−δ)})}`" of the display is not stated.

**Correction (as in Corollary 1).** The proof's choice of `P` and `k` (4.18) is made for
"`d^{1+δ} ln(1/ϵ) = M`" with `δ ∈ [0, 1]`, so `d ln(1/ϵ) ≤ M` is a hypothesis. Without it the display
fails: for `M = 1` and `ϵ` small enough that `P ∈ (d/36, d]`, `d̃ = 0` and every path oracle answers
Success on the cap `{‖x‖ ≤ 1, x₁ ≤ −1/2}`. A learner whose first query is `−e` then skips every
leaf in round 0, and the left side is `0`. `k ≤ d` keeps `U_P` a set of genuinely blocking leaves:
`Block_k` with `k > d` holds vacuously. -/
theorem eq_4_19 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-(d : ℝ)) →
      ∀ M : ℕ, (d : ℝ) * Real.log (1 / ε) ≤ M →
        (M : ℝ) * Real.logb 2 d ^ 4 / ((d : ℝ) ^ 2 * Real.logb 2 (1 / ε)) ≤ c₀ →
      ∀ alg : DetMemAlg d M, alg.IsMeasurable →
        let P : ℕ := 1 + ⌈(c₀ * (d : ℝ) ^ 2 * Real.log (1 / ε) /
          ((M : ℝ) * Real.logb 2 d ^ 5)) ^ ((1 : ℝ) / 8)⌉₊
      ∀ fin : (ℕ → Op d) → List (Vec d) → Vec d → Option (Vec d),
        (∀ Ebv : ℕ → Op d, IsValidAdaptive (Qset ε P Ebv) (fin Ebv)) →
        ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ν : Measure (Op d)) (Eb : ℕ → Ω → Op d) (ch : ℕ → List ℕ → ℕ → Ω → Op d),
        IsSkeleton d ε P μ ν Eb ch →
          ENNReal.ofReal (((d : ℝ) * Real.log (1 / ε)) ^ ((P : ℝ) / 4)) ≤
            ∑ n ∈ (Finset.range (numLeaves (Np d ε P) P)).filter (fun n =>
                PhaseBlock ε P alg fin μ Eb ch k (lam d P) (1 / (2 * P)) (leafOf (Np d ε P) P n)),
              μ {ω | GoodEvent d ε P (fun p => Eb p ω) (fun p u i => ch p u i ω)
                  (fin (fun p => Eb p ω)) ∧
                ¬ ∃ m, memV ε P alg (fun p u i => ch p u i ω) (fin (fun p => Eb p ω))
                    (leafOf (Np d ε P) P n) = some m ∧
                  pathOracle (delta d ε P) (fun p u i => ch p u i ω) (leafOf (Np d ε P) P n)
                    (alg.query m) = none} := by sorry

end MemQueryFeas
