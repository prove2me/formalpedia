-- Prove2me | Theorems.Thm_NumInvQH_Oblique_Supplement_proposition_3_17
-- name    : NumInvQH.Oblique.Supplement.proposition_3_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:45:39.959137+00:00
-- url     : https://prove2.me/theorems/3a521a18-3386-417b-a5b1-748fa7ae8643
-- title:
--   Proposition 3.17 — If X = S¹ is a nice numeraire
-- statement:
--   Let $S$ be a semimartingale market whose designated first asset $X$ is a nice numeraire. Put $\widehat S=S/X$, $d\widehat P/dP=X_T^2/E[X_T^2]$ and $\widetilde Z_t=E[X_T^2\mid\mathcal F_t]$, taking a càdlàg version when available and its conditional-expectation version otherwise. Then tame strategies coincide in the two models, both on $[0,T]$ and on every $[\tau,T]$; local square integrability transfers in both directions; $X$ is the wealth of a tame strategy; and $ZX$ is a $P$-martingale for every original deflator $Z$. Finally,
--   $$ZX/\widetilde Z\in M_2(\widehat S,\widehat P)\quad\Longleftrightarrow\quad Z\in M_2(S,P).$$
--   All five assertions are retained. This is the measure-and-numeraire transport used by the quadratic-hedging theorem.
--
--   Differences from the source:
--   - encoding: finite-horizon vector processes and stochastic equality → Fin-indexed coordinates, stopped extensions and indistinguishability on [0,T]; reason: this preserves the full finite-horizon domain, including null modifications and arbitrary finite dimension d ≥ 2
--   - encoding: the general predictable vector integral of [22, III.6.17] → elementary-sum construction followed by bounded predictable extension and Emery convergence of joint truncations; reason: this constructs general vector integration and retains cancellation; it does not impose coordinatewise integrability, absolute continuity of characteristics, or calculus axioms
--   - encoding: stochastic integrals, brackets, logarithms, exponentials and conditional processes → chosen genuine versions from explicit defining relations; reason: these quantities are unique up to indistinguishability on the stated domain; their outside-domain zero defaults are not hypotheses or replacement values for source objects
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 10–11, Proposition 3.17

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Numeraire

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NumInvQH.Oblique.Supplement

theorem proposition_3_17 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (h0 : ∀ A, MeasurableSet[ℱ 0] A → P A = 0 ∨ P A = 1)
    (T : ℝ≥0) {d : ℕ} (hd : 2 ≤ d) (S : Process Ω (Fin d → ℝ))
    (hS : Semi P ℱ T S) (first : Fin d) (hX : Nice P ℱ T (fun t ω => S t ω first)) :
    let X := fun t ω => S t ω first
    let Q := changedMeasure P T X
    let Sh := discounted S X
    let Zt := densityNumerator P ℱ T X
    (∀ θ, Tame P ℱ T S θ ↔ Tame Q ℱ T Sh θ) ∧
    (∀ (τ : BoundedStop ℱ T) θ, TameFrom P ℱ T S θ τ ↔ TameFrom Q ℱ T Sh θ τ) ∧
    (LocallySquareIntegrable P ℱ T S ↔ LocallySquareIntegrable Q ℱ T Sh) ∧
    (∃ φ, Tame P ℱ T S φ ∧ Same P T (wealth φ S) X) ∧
    (∀ Z, Deflator P ℱ T S Z → Martingale (stop T (fun t ω => Z t ω * X t ω)) ℱ P) ∧
    (∀ Z, Deflator Q ℱ T Sh (fun t ω => Z t ω * X t ω / Zt t ω) ↔ Deflator P ℱ T S Z) := by sorry

end NumInvQH.Oblique.Supplement
