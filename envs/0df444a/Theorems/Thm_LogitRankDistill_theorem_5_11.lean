-- Prove2me | Theorems.Thm_LogitRankDistill_theorem_5_11
-- name    : LogitRankDistill.theorem_5_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:00:25.452805+00:00
-- url     : https://prove2.me/theorems/a50045ba-d8c9-4886-805d-30fd296c86c7
-- title:
--   Theorem 5.11 — under E_oracle with an ε_apx-approximate oracle, Algorithm 1 learns M to total variation ε with Õ(T¹³d⁴|Σ|/ε⁴) queries in poly(N) time
-- statement:
--   Let $O_{\mathrm{logit}}$ be an $\varepsilon_{\mathrm{apx}}$-approximate logit oracle (Definition 4.1) for $M\in\Delta(\Sigma^T)$, fix $\delta,\varepsilon\in(0,1)$ with
--   $$\varepsilon\ge C\,\varepsilon_{\mathrm{apx}}KT^2d^{1/2}\log^{1/2}(K\alpha/\varepsilon_{\mathrm{apx}}),$$
--   and run Algorithm 1 with the parameters of §5.2. Then there is an event $E$ with $\Pr[E]\ge1-\delta$ such that on $E\cap E_{\mathrm{oracle}}$ Algorithm 1 returns data whose Algorithm-2 law $\hat M$ satisfies $D_{TV}(M,\hat M)\le\varepsilon$. Moreover the number of queries to $O_{\mathrm{logit}}$ and $M$ is at most
--   $$N=C\,\frac{T^{13}d^4|\Sigma|\,\Lambda^k}{\varepsilon^4},\qquad\Lambda=\log\Big(2+\frac{Td|\Sigma|\alpha}{\varepsilon\delta}\Big),$$
--   and the algorithm runs in $\mathrm{poly}(N)$ time: one fixed program of the oracle real RAM outputs Algorithm 1's data within $C N^C$ steps on every run.
--   It is the learning guarantee that Theorem 5.14 transfers to approximately low logit rank models.
--
--   **Formalization Note.** Constants $C,k$ and the §5.2 constants $C_{5.1},C_K,C_n,C_m$ are universal and fixed before the instance; $K$ in the hypothesis is the §5.2 value.
--
--   Differences from the source:
--   - generalization: "Algorithm 1" with its unspecified choices (spanner, program solution, Line 15 witness) → the correctness and the query bound hold for every admissible choice rule set (the solution rule shared with Algorithm 2); reason: every implementation of Algorithm 1 makes some admissible choices, so this specializes to it
--   - reading: Õ(·), Ω̃(·), poly log(α/δ), poly(N) → universal C > 0 and k ∈ ℕ fixed before the instance, with Λ = log(2 + Td|Σ|α/(εδ)) and the step bound C·N^C; reason: the hidden logarithmic and polynomial factors are absolute
--   - reading: "runs in poly(N) time" → one fixed admissible program of the oracle real RAM (SmaleNinth core + sample and logit instructions, no LP instruction) outputs Algorithm 1's data, under some admissible rules, within C·N^C steps on every run; reason: the paper names no machine (finding I4)
--   - reading: Line 17 stores L_oracle(h_{t,i} ∘ y) for y ∈ Σ; Algorithm 2 Line 6 reads L_{t,i}(y_t ∘ y) → Line 17 also stores the length-2 values (t ≤ T − 1); reason: otherwise Algorithm 2 is not determined by the output (finding I5)
--   - encoding: ⊥ / fail → Option: Algorithm 1 returns none; Algorithm 2's fail is none in the law on Option (Σ^T), counted as error; reason: same instances
--   - encoding: M with logits defined everywhere → FullSupport M; reason: only excludes cases where logits and the oracle are undefined
--   - encoding: queries and running time → bounds on every run (every stream of draws); reason: worst-case reading of "makes N queries"
--   - encoding: with probability 1 − δ → outer measure of the failure set ≤ δ (or a measurable event whose complement has measure ≤ δ); reason: equivalent formulation
--   - reading: "for an appropriate choice" / "sufficiently large constant" C_{5.1}, C_K, C_n and the Θ of DistSpanner → ∃ C51, CK, Cn, Cm > 0 chosen jointly with C, k; reason: universal constants of the analysis
--   - reading: Algorithm 1, Line 14: s, r ∈ [t + 1] with r ≥ s → the test ranges over 2 ≤ s ≤ t, s ≤ r ≤ t + 1 (LogitRankDistill.Algorithms); reason: at s = 1 the tested difference is 0 (c_1 = e_1, L_{1,i} = L_oracle(·)); at s = t + 1 no coefficients c_{t+1} exist
--   - reading: F̃_T = F̂_T ∪ (Σ ∘ F̂_{T+1}) with F̂_{T+1} never initialized; DistSpanner output "padded with duplicates" to d̄ vectors → F̂_{T+1} = ∅; the padding repeats the first spanner member; reason: Line 1 initializes F̂_t only for t ∈ [T]; any duplicate of a member leaves the spanned set unchanged
--   - encoding: d ∈ ℕ (the rank) and T a positive integer → 1 ≤ d and 1 ≤ T; reason: at d = 0 the logarithm in K (§5.2) is undefined; T ≥ 1 is Definition 1.1
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 30, Theorem 5.11

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_LogitRankDistill_Models
import Definitions.Def_LogitRankDistill_Spanners
import Definitions.Def_LogitRankDistill_Algorithms
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_LogitRankDistill_Machine

open MeasureTheory

namespace LogitRankDistill

/-- **Theorem 5.11** (p. 30): with an `ε_apx`-approximate logit oracle for `M` and
`δ, ε ∈ (0, 1)` with `ε ≥ C ε_apx K T² d^{1/2} log^{1/2}(Kα/ε_apx)`, and the parameters of §5.2,
there is an event `E` of probability at least `1 − δ` such that on `E ∩ E_oracle` Algorithm 1
returns data whose Algorithm-2 law `M̂` satisfies `D_TV(M, M̂) ≤ ε`. Moreover every run makes at
most `N = C T^{13} d⁴ |Σ| Λ^k/ε⁴` queries to `O_logit` and `M` (`Λ = log(2 + Td|Σ|α/(εδ))`, the
`poly log(α/δ)` and the logarithms hidden by `Õ`), and Algorithm 1 runs in `poly(N)` time: one
fixed admissible program of the oracle real RAM computes its output (under some admissible choice
rules) within `C N^C` steps on every run. Stated for every admissible choice of rules. -/
theorem theorem_5_11 :
    ∃ (C : ℝ) (k : ℕ) (C51 CK Cn Cm : ℝ), 0 < C ∧ 0 < C51 ∧ 0 < CK ∧ 0 < Cn ∧ 0 < Cm ∧
    ∃ P : Program, Admissible P ∧
    ∀ (Tok : Type) [Fintype Tok] [DecidableEq Tok] [MeasurableSpace Tok]
      [MeasurableSingletonClass Tok] (T d : ℕ) (α εapx ε δ : ℝ) (M : PMF (Fin T → Tok))
      (O : List Tok → Tok → ℝ) (p : Params),
      1 ≤ T → 1 ≤ d → 0 < α → 0 < εapx → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      FullSupport M → IsApproxOracle M εapx O →
      Section52 C51 CK Cn Cm T d α εapx ε δ p →
      C * εapx * p.K * (T : ℝ) ^ 2 * Real.sqrt d *
          Real.sqrt (Real.log (p.K * α / εapx)) ≤ ε →
      (∀ R : Rules Tok, R.Admissible →
        (∃ E : Set (ℕ → Fin T → Tok), MeasurableSet E ∧
          streamLaw M Eᶜ ≤ ENNReal.ofReal δ ∧
          ∀ ω ∈ E, (⟨T, O, ω, p, R⟩ : Ctx Tok).OracleEvent d α εapx →
            ∃ D, (⟨T, O, ω, p, R⟩ : Ctx Tok).output = some D ∧
              IsingLTL.BeliefProp.tvDist (modelLaw M) (alg2Law R.lp p.β D) ≤ ε) ∧
        ∀ ω : ℕ → Fin T → Tok,
          ((⟨T, O, ω, p, R⟩ : Ctx Tok).numQueries + (⟨T, O, ω, p, R⟩ : Ctx Tok).run.cur : ℝ) ≤
            C * (T : ℝ) ^ 13 * (d : ℝ) ^ 4 * Fintype.card Tok *
              Real.log (2 + T * d * Fintype.card Tok * α / (ε * δ)) ^ k / ε ^ 4) ∧
      ∃ R : Rules Tok, R.Admissible ∧ ∀ ω : ℕ → Fin T → Tok,
        HaltsWithin P O ω (algInput T (Fintype.card Tok) d α ε δ p)
          (C * (C * (T : ℝ) ^ 13 * (d : ℝ) ^ 4 * Fintype.card Tok *
            Real.log (2 + T * d * Fintype.card Tok * α / (ε * δ)) ^ k / ε ^ 4) ^ C) ∧
        mOutput P O ω (algInput T (Fintype.card Tok) d α ε δ p) =
          serialize T (⟨T, O, ω, p, R⟩ : Ctx Tok).output := by sorry

end LogitRankDistill
