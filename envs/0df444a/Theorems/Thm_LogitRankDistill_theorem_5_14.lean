-- Prove2me | Theorems.Thm_LogitRankDistill_theorem_5_14
-- name    : LogitRankDistill.theorem_5_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:00:31.601325+00:00
-- url     : https://prove2.me/theorems/7d688b73-d02c-4b5c-bc5f-d28b5c4b3cae
-- title:
--   Theorem 5.14 — an ε_avg-approximately α-bounded logit rank d model is learned to total variation ε⋆ with probability 1 − δ⋆ from Õ(T¹³d⁴|Σ|⁴/ε⋆⁴) exact logit queries in poly(N) time
-- statement:
--   Fix $\varepsilon_\star,\delta_\star\in(0,1)$. Let $M\in\Delta(\Sigma^T)$ have full support and $\varepsilon_{\mathrm{avg}}$-approximate $\alpha$-bounded logit rank $d$ (Definition 4.3) with
--   $$\varepsilon_\star\ge\tilde\Omega\Big(\big(T^{31}d^{9.5}|\Sigma|^4\,\mathrm{poly}\log(\alpha/\delta)\cdot\varepsilon_{\mathrm{avg}}\big)^{1/9}\Big),$$
--   and let $O_{\mathrm{logit}}$ be an exact logit oracle for $M$ (Definition 1.7). Then for an appropriate choice of parameters, when Algorithm 1 is run with samples from $M$ and the oracle $O_{\mathrm{logit}}$, with probability at least $1-\delta_\star$ it returns data whose Algorithm-2 law $\hat M$ satisfies $D_{TV}(\hat M,M)\le\varepsilon_\star$; it makes
--   $$N=\tilde O\Big(\frac{T^{13}d^4|\Sigma|^4\,\mathrm{poly}\log(\alpha/\delta_\star)}{\varepsilon_\star^4}\Big)$$
--   queries to $O_{\mathrm{logit}}$ and runs in $\mathrm{poly}(N)$ time.
--
--   In Lean, with $\Lambda=\log(2+Td|\Sigma|\alpha/(\varepsilon_\star\delta_\star))$: there are universal $C>0$, $k\in\mathbb N$, a parameter map of $(T,d,|\Sigma|,\alpha,\varepsilon_\star,\delta_\star)$ and one admissible oracle-real-RAM program such that for every finite $\Sigma$, $T,d\ge1$, $\alpha>0$, $\varepsilon_\star,\delta_\star\in(0,1)$, $\varepsilon_{\mathrm{avg}}\ge0$ with $\varepsilon_\star^9\ge C\,T^{31}d^{9.5}|\Sigma|^4\Lambda^k\varepsilon_{\mathrm{avg}}$, every such $M$ and every exact oracle: (i) for every admissible choice of rules the failure probability is at most $\delta_\star$; (ii) every run makes at most $N=C\,T^{13}d^4|\Sigma|^4\Lambda^k/\varepsilon_\star^4$ oracle calls; (iii) the program outputs Algorithm 1's data under some admissible rules within $C\,N^C$ steps on every run. This is the paper's main result (Theorem 1.2 is its informal version).
--
--   **Formalization Note.** Failure of Algorithm 1 ($\bot$) and of Algorithm 2 (fail) count as error: $\hat M$ lives on $\Sigma^T\cup\{\mathrm{fail}\}$. The probability is the outer measure of the failure set of streams under `streamLaw M`.
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
--   - reading: "for an appropriate choice of parameters" → an explicit parameter map from (T, d, |Σ|, α, ε⋆, δ⋆) alone, chosen before the instance; reason: parameters may not depend on M, ε_avg or the oracle
--   - generalization: ε_avg-approximate logit rank (Definition 4.3, ε > 0) → ε_avg ≥ 0; reason: the case ε_avg = 0 follows from the case of small ε_avg > 0, so this specializes to the printed statement
--   - reading: Definition 1.6 at s = 0: h ∼ M_{1:−1} × Unif(Σ) → the history is empty at s = 0; reason: there is no position 0
--   - reading: ε⋆ ≥ Ω̃((T³¹ d^{9.5} |Σ|⁴ poly log(α/δ) ε_avg)^{1/9}) → ε⋆⁹ ≥ C T³¹ d^{9.5} |Σ|⁴ Λ^k ε_avg; reason: raising both sides to the ninth power; Λ carries no 1/ε_avg and no power of 1/δ⋆, as printed (finding I3)
--   - reading: Algorithm 1, Line 14: s, r ∈ [t + 1] with r ≥ s → the test ranges over 2 ≤ s ≤ t, s ≤ r ≤ t + 1 (LogitRankDistill.Algorithms); reason: at s = 1 the tested difference is 0 (c_1 = e_1, L_{1,i} = L_oracle(·)); at s = t + 1 no coefficients c_{t+1} exist
--   - reading: F̃_T = F̂_T ∪ (Σ ∘ F̂_{T+1}) with F̂_{T+1} never initialized; DistSpanner output "padded with duplicates" to d̄ vectors → F̂_{T+1} = ∅; the padding repeats the first spanner member; reason: Line 1 initializes F̂_t only for t ∈ [T]; any duplicate of a member leaves the spanned set unchanged
--   - encoding: d ∈ ℕ (the rank) and T a positive integer → 1 ≤ d and 1 ≤ T; reason: at d = 0 the logarithm in K (§5.2) is undefined; T ≥ 1 is Definition 1.1
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 33, Theorem 5.14

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_LogitRankDistill_Models
import Definitions.Def_LogitRankDistill_Spanners
import Definitions.Def_LogitRankDistill_Algorithms
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_LogitRankDistill_Machine

open MeasureTheory

namespace LogitRankDistill

/-- **Theorem 5.14** (p. 33). There are universal constants `C > 0`, `k ∈ ℕ`, a choice of the
parameters of Algorithm 1 from `(T, d, |Σ|, α, ε⋆, δ⋆)` alone, and one admissible program of the
oracle real RAM, such that: for every finite alphabet `Σ`, `T, d ≥ 1`, `α > 0`, `ε⋆, δ⋆ ∈ (0, 1)`,
`ε_avg ≥ 0` and every full-support `M ∈ Δ(Σ^T)` of `ε_avg`-approximate `α`-bounded logit rank `d`
with `ε⋆^9 ≥ C T^{31} d^{9.5} |Σ|⁴ Λ^k ε_avg`, `Λ = log(2 + Td|Σ|α/(ε⋆δ⋆))`, and every exact logit
oracle `O` for `M`:
(i) for every admissible choice of rules, with probability at least `1 − δ⋆` Algorithm 1 returns and
the law `M̂` of Algorithm 2 on its output satisfies `D_TV(M̂, M) ≤ ε⋆`;
(ii) every run makes at most `N = C T^{13} d⁴ |Σ|⁴ Λ^k/ε⋆⁴` queries to `O`;
(iii) the program computes Algorithm 1's output (under some admissible choice of rules) and halts
within `C N^C` steps on every run. -/
theorem theorem_5_14 :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∃ par : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ → Params,
    ∃ P : Program, Admissible P ∧
    ∀ (Tok : Type) [Fintype Tok] [DecidableEq Tok] [MeasurableSpace Tok]
      [MeasurableSingletonClass Tok] (T d : ℕ) (α εs δs εavg : ℝ) (M : PMF (Fin T → Tok))
      (O : List Tok → Tok → ℝ),
      1 ≤ T → 1 ≤ d → 0 < α → 0 < εs → εs < 1 → 0 < δs → δs < 1 → 0 ≤ εavg →
      FullSupport M → HasApproxBoundedLogitRank M εavg α d → IsExactOracle M O →
      C * (T : ℝ) ^ 31 * (d : ℝ) ^ (19 / 2 : ℝ) * (Fintype.card Tok : ℝ) ^ 4 *
          Real.log (2 + T * d * Fintype.card Tok * α / (εs * δs)) ^ k * εavg ≤ εs ^ 9 →
      (∀ R : Rules Tok, R.Admissible →
        streamLaw M {ω | ¬ ∃ D,
            (⟨T, O, ω, par T d (Fintype.card Tok) α εs δs, R⟩ : Ctx Tok).output = some D ∧
            IsingLTL.BeliefProp.tvDist
              (alg2Law R.lp (par T d (Fintype.card Tok) α εs δs).β D) (modelLaw M) ≤ εs} ≤
          ENNReal.ofReal δs ∧
        ∀ ω : ℕ → Fin T → Tok,
          ((⟨T, O, ω, par T d (Fintype.card Tok) α εs δs, R⟩ : Ctx Tok).numQueries : ℝ) ≤
            C * (T : ℝ) ^ 13 * (d : ℝ) ^ 4 * (Fintype.card Tok : ℝ) ^ 4 *
              Real.log (2 + T * d * Fintype.card Tok * α / (εs * δs)) ^ k / εs ^ 4) ∧
      ∃ R : Rules Tok, R.Admissible ∧ ∀ ω : ℕ → Fin T → Tok,
        HaltsWithin P O ω
            (algInput T (Fintype.card Tok) d α εs δs (par T d (Fintype.card Tok) α εs δs))
            (C * (C * (T : ℝ) ^ 13 * (d : ℝ) ^ 4 * (Fintype.card Tok : ℝ) ^ 4 *
              Real.log (2 + T * d * Fintype.card Tok * α / (εs * δs)) ^ k / εs ^ 4) ^ C) ∧
        mOutput P O ω
            (algInput T (Fintype.card Tok) d α εs δs (par T d (Fintype.card Tok) α εs δs)) =
          serialize T (⟨T, O, ω, par T d (Fintype.card Tok) α εs δs, R⟩ : Ctx Tok).output := by sorry

end LogitRankDistill
