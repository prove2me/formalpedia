-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_theorem_6_3
-- name    : MulticalibrationERM.Oracle.theorem_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:53:17.630738+00:00
-- url     : https://prove2.me/theorems/73e2f1af-3f47-410b-9c26-91ebd4c5f864
-- title:
--   Theorem 6.3 — cell rounding for VC classes, ordinary and swap clauses
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $Q$ be a randomized predictor on $\Lambda$; $O$ a finite set of inputs, each with an interval $I_x=[ylo_x,yhi_x]$ of length at most $2r_x$ containing $f^\star(x)$, with $Q_x$ supported within distance $1/K$ of $I_x$; $P$ a finite measurable partition of $X$ whose cells include the singletons $\{x\}$, $x\in O$, the remaining cells forming $P_{\mathrm{rest}}$; $V_P=\sum_{x\in O}\omega_x^2r_x^2+\sum_{R\in P_{\mathrm{rest}}}D_X(R)^2$; $G_x(\xi)\sim Q_x$, independent seeds $\xi_R$ per cell, $p(x)=G_x(\xi_{R(x)})$. With probability at least $1-\delta$ over the seeds,
--   $$\mathrm{MC}(p)\le\mathrm{MC}(Q)+C\sqrt{V_P\,(d+m+\log(2/\delta))}+\frac2K,\qquad \mathrm{SMC}(p)\le\mathrm{SMC}(Q)+C\sqrt{V_P\,(md+\log(2/\delta))}+\frac2K,$$
--   and the terms $2/K$ can be omitted when $O=\varnothing$.
--
--   Differences from the source:
--   - reading: f⋆(x) = E[Y | X = x] for x ∈ O → the condition f⋆(x) ∈ I_x is imposed (or asserted) at the inputs x ∈ O with D_X({x}) > 0; f⋆ is defined at atoms as E[Y 1{X = x}]/D_X({x}); reason: a conditional mean is determined only up to D_X-null sets, so at an input of mass zero its value is not determined; at atoms it is
--   - encoding: a partition consisting of the singletons {x}, x ∈ O, and finitely many further measurable cells covering X ∖ O → a map cell : X → ι into a finite type with measurable fibers, whose fiber through each x ∈ O is {x}; P_rest are the fibers not through O (empty fibers contribute 0); reason: same partitions
--   - encoding: the terms 2/K can be omitted when O = ∅ → the additive term is 2/K if O is nonempty and 0 if O = ∅; reason: the two cases of the sentence
--   - reading: maps G_x with G_x(ξ) ∼ Q_x → (x, ξ) ↦ G_x(ξ) jointly measurable; reason: the errors of p are expectations over X; standing measurability assumption
--   - generalization: a class of VC dimension d (standing assumption, p. 12) → any class of VC dimension at most d (with d ≥ 1); reason: every class of VC dimension exactly d is an instance
--   - encoding: auditors h : X → {−1,+1} → h : X → Bool with value pm (h x) ∈ {1, −1} (true ↦ +1); reason: relabelling of the two values; every auditor is an instance
--   - reading: the standard measurability conditions for suprema over H (p. 12) → every auditor measurable and the class pointwise measurable (a countable subclass whose sequences converge pointwise to every member); reason: the paper names no specific condition; pointwise measurability is the standard one under which the suprema are suprema over a countable class
--   - encoding: probability of the failure event → the measure applied to the failure set, i.e. its outer measure when the set is not measurable; reason: equal to the probability when the event is measurable; an outer-measure bound is never weaker
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 33, Theorem 6.3

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_OEMC

open MeasureTheory ProbabilityTheory

namespace MulticalibrationERM.Oracle

/-- Theorem 6.3 (p. 33): cell rounding for VC classes, both clauses. `Q` is a randomized predictor
on `Λ`; `O` a finite set of inputs, each with an interval `I_x = [ylo_x, yhi_x]` of length at most
`2 r_x` containing `f⋆(x)` (at the inputs of positive mass, where `f⋆` is determined), and `Q_x`
supported within `1/K` of `I_x`; the partition `P` (cells `{x | cell x = i}`, finitely many,
measurable) has the singletons `{x}`, `x ∈ O`, among its cells; `V_P = ∑_{x ∈ O} ω_x² r_x² +
∑_{R ∈ P_rest} D_X(R)²`. With independent seeds `ξ_R ∼ μΞ` per cell, `G_x(ξ) ∼ Q_x` and
`p(x) = G_x(ξ_{R(x)})`: with probability at least `1 − δ` over the seeds,
`MC(p) ≤ MC(Q) + C √(V_P (d + m + log(2/δ))) + 2/K` and
`SMC(p) ≤ SMC(Q) + C √(V_P (m d + log(2/δ))) + 2/K`, and the terms `2/K` can be omitted when
`O = ∅` (they are present exactly when `O` is nonempty). -/
theorem theorem_6_3 :
    ∃ C : ℝ, 0 < C ∧
    ∀ {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ), IsAuditorClass H d →
    ∀ (D : LabeledDist X) (K : ℕ), 1 ≤ K → ∀ (Q : X → Fin (K + 1) → ℝ), IsGridPred K Q →
    ∀ (O : Finset X) (ylo yhi r : X → ℝ),
      (∀ x ∈ O, ylo x ≤ yhi x ∧ yhi x - ylo x ≤ 2 * r x) →
      (∀ x ∈ O, 0 < D.atom x → D.fstar x ∈ Set.Icc (ylo x) (yhi x)) →
      (∀ x ∈ O, SupportNear K Q x (ylo x) (yhi x)) →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (cell : X → ι), (∀ i, MeasurableSet {x | cell x = i}) →
      (∀ x ∈ O, {y | cell y = cell x} = {x}) →
    ∀ {Ξ : Type} [MeasurableSpace Ξ] (μΞ : Measure Ξ) [IsProbabilityMeasure μΞ]
      (Gq : X → Ξ → Fin (K + 1)), Measurable (Function.uncurry Gq) →
      (∀ x i, μΞ {ξ | Gq x ξ = i} = ENNReal.ofReal (Q x i)) →
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      (Measure.pi fun _ : ι => μΞ)
          {ξ | ¬ (gridMC D H K (detPred K (cellRound cell Gq ξ)) ≤
                gridMC D H K Q +
                  C * Real.sqrt ((∑ x ∈ O, D.atom x ^ 2 * r x ^ 2 +
                      ∑ i ∈ Finset.univ.filter (fun i => ∀ x ∈ O, cell x ≠ i),
                        D.massX {y | cell y = i} ^ 2) *
                    (d + (K + 1) + Real.log (2 / δ))) +
                  (if O.Nonempty then 2 / (K : ℝ) else 0) ∧
              gridSMC D H K (detPred K (cellRound cell Gq ξ)) ≤
                gridSMC D H K Q +
                  C * Real.sqrt ((∑ x ∈ O, D.atom x ^ 2 * r x ^ 2 +
                      ∑ i ∈ Finset.univ.filter (fun i => ∀ x ∈ O, cell x ≠ i),
                        D.massX {y | cell y = i} ^ 2) *
                    ((K + 1) * d + Real.log (2 / δ))) +
                  (if O.Nonempty then 2 / (K : ℝ) else 0))} ≤
        ENNReal.ofReal δ := by sorry

end MulticalibrationERM.Oracle
