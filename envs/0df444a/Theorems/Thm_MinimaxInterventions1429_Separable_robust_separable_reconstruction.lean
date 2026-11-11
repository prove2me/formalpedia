-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_robust_separable_reconstruction
-- name    : MinimaxInterventions1429.Separable.robust_separable_reconstruction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:56.672725+00:00
-- url     : https://prove2.me/theorems/be071528-be3d-4474-9b60-3fe5be76c590
-- title:
--   Theorem 3.5 — robust separable reconstruction
-- statement:
--   Let $m,k\ge2$, $\alpha\ge0$, and integer $T\ge1$. The concrete Section 3.2 algorithm is deterministic, sees only returned bits, and makes at most $(mk-1)T$ calls with separable surcharges of max-entry norm at most $5$. For every $L\in[0,1]^{m\times k}$ and every oracle whose answers in this run are $\alpha$-accurate, each returned table and root $g_0$ satisfy
--
--   $$d_q(\widehat L,L)\le17\alpha+\tfrac{17}{2}2^{-T},\qquad
--   \|\widehat L-(L-L_{g_01}\mathbf1)\|_\infty\le22\alpha+11\cdot2^{-T}.$$
--
--   It returns a table whenever $\Lambda(L)>44\alpha+18\cdot2^{-T}$. The accuracy assertions hold whenever it returns, including below this sufficient threshold. The statement also verifies the computed plan: after planning accepts, each edge has an eligible column, and its parent tree has diameter at most three and root depth at most two, even on other bit strings.
--
--   For a random synopsis with a public deterministic decoder simultaneously $\alpha$-accurate for every $B\in\mathcal S$ on one event of probability at least $1-\beta$, the same returned-table and nonfailure conclusions hold on an event of probability at least $1-\beta$. The identical guarantee holds for an interactive transcript jointly accurate on one such event. Here $0\le\beta\le1$; all events and public output maps are measurable as stipulated in Section 2. For every database domain, adjacency relation, and $\varepsilon\ge0$, $0\le\delta<1$, deterministic reconstruction preserves $(\varepsilon,\delta)$-privacy of the single synopsis or of the whole interactive transcript on the full database domain. The privacy guarantee covers the optional-table output, including its observable failure symbol. There is no privacy composition or change in $\beta$.
--
--   This theorem states both quotient and anchored guarantees and the source's synopsis and interactive consequences, with arbitrary adversarial history dependence.
--
--   Differences from the source:
--   - encoding: rows and actions indexed from 1 with m,k ≥ 2 → Fin m and Fin k, source column 1 represented by 0, with explicit 2 ≤ m and 2 ≤ k; reason: order-preserving relabeling; closed-simplex mixtures and arbitrary real arrays retain every source instance
--   - encoding: minimum of F on the closed simplex and quotient distance defined by an infimum over scalar shifts → optimality compared against every simplex point and quotient distance equal to half the oscillation; reason: the finite nonempty simplex is compact and the objective continuous; Eq. (2) gives the identical quotient distance without default-valued infima
--   - encoding: adversarial bit answers accurate only along the realized calls → a finite bit-query program evaluated with an arbitrary history-dependent oracle and a witness for each recorded bit; reason: the program observes only bits and public queries; weak ties admit both bits and no common witness or numerical response is assumed
--   - encoding: possibly randomized procedures, with all events and transcripts measurable → arbitrary probability spaces for random seeds, measurable common response maps and exact bit kernels, and explicit measurable output or success-event conditions; probabilities in ENNReal; reason: these are Section 2 standing measurability conventions, not restrictions to finite seeds, rational queries or fixed tie-breaking
--   - encoding: deterministic public planning and alignment from Section 3.2 → first-extremizer scans, breadth-first alignment and explicit totality and tree-invariant conclusions; reason: fixed tie-breaking and traversal implement the source algorithm; absent-column failure is impossible after planning accepts
--   - encoding: a private synopsis or a private, jointly accurate entire interactive transcript → decoded bit-program evaluation or transcript replay, unchanged beta bounds, and event-form epsilon-delta privacy of the measurable pushforward law; reason: the optional-table release retains the source failure symbol; the high-interaction guarantee requires actual success, and the full-domain privacy parameters are unchanged
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Theorem 3.5, printed p.11 (PDF p.13)

import Definitions.Def_MinimaxInterventions1429_Separable_ObservationLaws
set_option autoImplicit false

namespace MinimaxInterventions1429.Separable

theorem robust_separable_reconstruction {m k : ℕ} [NeZero m] [NeZero k]
    (hm : 2 ≤ m) (hk : 2 ≤ k) (α : ℝ) (hα : 0 ≤ α) (T : ℕ) (hT : 1 ≤ T) :
    (reconstruction m k α T).maxQueries ≤ (m * k - 1) * T ∧
    (reconstruction m k α T).queriesSatisfy (fun q => Allowed q.surcharge) ∧
    (∀ (L : Table m k), InCube L → ∀ O : BitOracle m k,
      AccurateHistory L α ((reconstruction m k α T).run O []).2 →
      (∀ g M, ((reconstruction m k α T).run O []).1 = some (g, M) →
        quotientDist M L ≤ 17 * α + (17 : ℝ) / 2 * eta T ∧
        entryNorm (M - (fun r h => L r h - L g 0)) ≤ 22 * α + 11 * eta T) ∧
      (44 * α + 18 * eta T < interaction L →
        ∃ g M, ((reconstruction m k α T).run O []).1 = some (g, M))) ∧
    (∀ O : BitOracle m k,
      let w := ((contrastPhase m k α T).run O []).1
      ∀ plan, planAnchors α T w = some plan →
        (∀ g, g ≠ plan.root →
          (eligibleColumn w (effectiveTolerance α (2 * α + eta T)) g (plan.parent g)).isSome = true) ∧
        ∃ tree : ParentTree m, tree.root = plan.root ∧ tree.parent = plan.parent ∧
          tree.diameterAtMostThree ∧ (∀ g, tree.rank g ≤ 2)) ∧
    (∀ {S : Type*} [MeasurableSpace S] (μ : MeasureTheory.Measure S)
      [MeasureTheory.IsProbabilityMeasure μ] (Dec : S → Table m k → Mixture k)
      (L : Table m k), InCube L → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      MeasurableSet {s | SimultaneouslyAccurate Dec L α s} →
      MeasurableSet {s |
        (∀ g M, (synopsisRun Dec α T s).1 = some (g, M) →
          quotientDist M L ≤ 17 * α + (17 : ℝ) / 2 * eta T ∧
          entryNorm (M - (fun r h => L r h - L g 0)) ≤ 22 * α + 11 * eta T) ∧
        (44 * α + 18 * eta T < interaction L →
          ∃ g M, (synopsisRun Dec α T s).1 = some (g, M))} →
      ENNReal.ofReal (1 - β) ≤ μ {s | SimultaneouslyAccurate Dec L α s} →
      ENNReal.ofReal (1 - β) ≤ μ {s |
        (∀ g M, (synopsisRun Dec α T s).1 = some (g, M) →
          quotientDist M L ≤ 17 * α + (17 : ℝ) / 2 * eta T ∧
          entryNorm (M - (fun r h => L r h - L g 0)) ≤ 22 * α + 11 * eta T) ∧
        (44 * α + 18 * eta T < interaction L →
          ∃ g M, (synopsisRun Dec α T s).1 = some (g, M))}) ∧
    (∀ (μ : MeasureTheory.Measure (History m k)) [MeasureTheory.IsProbabilityMeasure μ]
      (L : Table m k), InCube L → ∀ β : ℝ, 0 ≤ β → β ≤ 1 →
      MeasurableSet {hist | IsTranscript α T hist ∧ AccurateHistory L α hist} →
      MeasurableSet {hist |
        (∀ g M, (replay α T hist).1 = some (g, M) →
          quotientDist M L ≤ 17 * α + (17 : ℝ) / 2 * eta T ∧
          entryNorm (M - (fun r h => L r h - L g 0)) ≤ 22 * α + 11 * eta T) ∧
        (44 * α + 18 * eta T < interaction L →
          ∃ g M, (replay α T hist).1 = some (g, M))} →
      ENNReal.ofReal (1 - β) ≤ μ {hist | IsTranscript α T hist ∧ AccurateHistory L α hist} →
      ENNReal.ofReal (1 - β) ≤ μ {hist |
        (∀ g M, (replay α T hist).1 = some (g, M) →
          quotientDist M L ≤ 17 * α + (17 : ℝ) / 2 * eta T ∧
          entryNorm (M - (fun r h => L r h - L g 0)) ≤ 22 * α + 11 * eta T) ∧
        (44 * α + 18 * eta T < interaction L →
          ∃ g M, (replay α T hist).1 = some (g, M))}) ∧
    (∀ {D S : Type*} [MeasurableSpace S] (Dec : S → Table m k → Mixture k)
      (adj : D → D → Prop) (ε δ : ℝ) (mechanism : D → MeasureTheory.Measure S),
      0 ≤ ε → 0 ≤ δ → δ < 1 →
      (∀ d, MeasureTheory.IsProbabilityMeasure (mechanism d)) →
      Measurable (synopsisOutput Dec α T : S → Option (Table m k)) →
      DifferentiallyPrivate adj ε δ mechanism →
      DifferentiallyPrivate adj ε δ
        (fun d => MeasureTheory.Measure.map (synopsisOutput Dec α T) (mechanism d))) ∧
    (∀ {D : Type*} (adj : D → D → Prop) (ε δ : ℝ)
      (mechanism : D → MeasureTheory.Measure (History m k)),
      0 ≤ ε → 0 ≤ δ → δ < 1 →
      (∀ d, MeasureTheory.IsProbabilityMeasure (mechanism d)) →
      Measurable (transcriptOutput α T : History m k → Option (Table m k)) →
      DifferentiallyPrivate adj ε δ mechanism →
      DifferentiallyPrivate adj ε δ
        (fun d => MeasureTheory.Measure.map (transcriptOutput α T) (mechanism d))) := by sorry

end MinimaxInterventions1429.Separable
