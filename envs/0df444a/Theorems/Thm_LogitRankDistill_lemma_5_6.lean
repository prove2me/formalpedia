-- Prove2me | Theorems.Thm_LogitRankDistill_lemma_5_6
-- name    : LogitRankDistill.lemma_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:59:52.453845+00:00
-- url     : https://prove2.me/theorems/29f1c722-f43b-4bf3-9443-22b77f6a2b6a
-- title:
--   Lemma 5.6 — with K ≥ C·Td log(βdαT/ε_apx) epochs, on E_oracle ∩ E_spanner ∩ E_5.6 some epoch passes every Line 14 test
-- statement:
--   Suppose $K\ge C\,Td\log(\beta d\alpha T/\varepsilon_{\mathrm{apx}})$ for a sufficiently large constant $C$, the other parameters being those of §5.2 and $O$ an $\varepsilon_{\mathrm{apx}}$-approximate logit oracle for $M$. Then there is an event $E_{5.6}$ with
--   $$\Pr[E_{5.6}]\ge1-\delta/4$$
--   such that on $E_{\mathrm{oracle}}\cap E_{\mathrm{spanner}}\cap E_{5.6}$ there is an epoch $k\in[K]$ at which the if statement on Line 14 is False for every step $t$ (so Algorithm 1 returns).
--   With Lemma 5.8 this is what makes Algorithm 1 terminate with useful data in Theorem 5.11.
--
--   **Formalization Note.** $E_{5.6}$ is a measurable set of streams; "some epoch passes" is: some executed epoch ends with outcome `passed`. The constants $C_{5.1},C_n,C_m$ of §5.2 are chosen together with $C$.
--
--   Differences from the source:
--   - reading: "for a sufficiently large constant C", with C_{5.1}, C_n of §5.2 and DistSpanner's Θ → ∃ C, C51, Cn, Cm > 0 chosen jointly before the instance; reason: all are universal constants of the analysis
--   - reading: K an integer, n = C_n log(TK/δ)/γ_thres → n = ⌈C_n log(TK/δ)/γ_thres⌉, m(N) = ⌈C_m(N/η)² log(N/(δ′η))⌉; reason: integer parameters; rounding up
--   - encoding: M with logits defined everywhere → FullSupport M; reason: only excludes cases where the logits are undefined
--   - encoding: an event E_5.6 with probability ≥ 1 − δ/4 → a measurable set of streams whose complement has measure ≤ δ/4; reason: equivalent formulation
--   - generalization: Algorithm 1 with its unspecified choices (spanner, program solution, Line 15 witness) → every admissible choice rule set; reason: every implementation of Algorithm 1 makes some admissible choices, so this specializes to it
--   - reading: Algorithm 1, Line 14: s, r ∈ [t + 1] with r ≥ s → the test ranges over 2 ≤ s ≤ t, s ≤ r ≤ t + 1 (LogitRankDistill.Algorithms); reason: at s = 1 the tested difference is 0 (c_1 = e_1, L_{1,i} = L_oracle(·)); at s = t + 1 no coefficients c_{t+1} exist
--   - reading: F̃_T = F̂_T ∪ (Σ ∘ F̂_{T+1}) with F̂_{T+1} never initialized; DistSpanner output "padded with duplicates" to d̄ vectors → F̂_{T+1} = ∅; the padding repeats the first spanner member; reason: Line 1 initializes F̂_t only for t ∈ [T]; any duplicate of a member leaves the spanned set unchanged
--   - reading: the if statement in Line 14 evaluates to False for all steps t ∈ [T] → some executed epoch has outcome `passed`: the program is feasible for every u (Line 11) and Line 14 finds no witness, at every t ∈ [T − 1]; reason: Line 14 is reached at step t only after Line 11, and the loop of Line 9 runs over t ≤ T − 1
--   - encoding: d ∈ ℕ (the rank) and T a positive integer → 1 ≤ d and 1 ≤ T; reason: at d = 0 the logarithm in K (§5.2) is undefined; T ≥ 1 is Definition 1.1
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 25, Lemma 5.6

import Mathlib
import Definitions.Def_LogitRankDistill_Models
import Definitions.Def_LogitRankDistill_Spanners
import Definitions.Def_LogitRankDistill_Algorithms

open MeasureTheory

namespace LogitRankDistill

/-- **Lemma 5.6** (p. 25): if `K ≥ C T d log(βdαT/ε_apx)` for a sufficiently large constant `C`
(the other parameters as in §5.2), there is an event `E_{5.6}` of probability at least `1 − δ/4`
such that on `E_oracle ∩ E_spanner ∩ E_{5.6}` some epoch `k ∈ [K]` passes the Line 14 test at every
step (the run returns). The constants `C_{5.1}`, `C_n`, `C_m` of §5.2 and Algorithm 3 are chosen
together with `C`; `O` is an `ε_apx`-approximate logit oracle for `M` (§5.2). -/
theorem lemma_5_6 :
    ∃ (C C51 Cn Cm : ℝ), 0 < C ∧ 0 < C51 ∧ 0 < Cn ∧ 0 < Cm ∧
    ∀ (Tok : Type) [Fintype Tok] [DecidableEq Tok] [MeasurableSpace Tok]
      [MeasurableSingletonClass Tok] (T d : ℕ) (α εapx ε δ : ℝ) (M : PMF (Fin T → Tok))
      (O : List Tok → Tok → ℝ) (p : Params) (R : Rules Tok),
      1 ≤ T → 1 ≤ d → 0 < α → 0 < εapx → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      FullSupport M → IsApproxOracle M εapx O →
      Section52Rest C51 Cn Cm T d α εapx ε δ p →
      C * T * d * Real.log (p.β * d * α * T / εapx) ≤ p.K → R.Admissible →
      ∃ E : Set (ℕ → Fin T → Tok), MeasurableSet E ∧
        streamLaw M Eᶜ ≤ ENNReal.ofReal (δ / 4) ∧
        ∀ ω ∈ E, (⟨T, O, ω, p, R⟩ : Ctx Tok).OracleEvent d α εapx →
          (⟨T, O, ω, p, R⟩ : Ctx Tok).SpannerEvent M →
          ∃ e ∈ (⟨T, O, ω, p, R⟩ : Ctx Tok).run.epochs, e.outcome = Outcome.passed := by sorry

end LogitRankDistill
