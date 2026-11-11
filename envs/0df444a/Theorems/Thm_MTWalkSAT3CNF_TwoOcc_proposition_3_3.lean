-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_proposition_3_3
-- name    : MTWalkSAT3CNF.TwoOcc.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:27:27.565405+00:00
-- url     : https://prove2.me/theorems/9ec1c831-3425-4971-b5e0-3e7637112986
-- title:
--   Proposition 3.3 — same-sign splitting can only increase the WalkSAT time
-- statement:
--   Let $\Delta(F)\le2$ and let $F^\sharp$ be obtained by splitting every variable $x$ with two same-sign occurrences into fresh variables $x^{(1)},x^{(2)}$ (one for each occurrence). Given an initial assignment $X_0$ on $V$, let $Y_0$ copy $X_0(x)$ to both $x^{(1)}$ and $x^{(2)}$ and agree with $X_0$ elsewhere. Write $T_{WS}(G;\sigma,R)$ for the termination time of WalkSAT on $G$ from $\sigma$ under an adaptive clause-selection rule $R$. Then
--
--   $$\forall X_0\in\{0,1\}^V,\ \forall R\text{ on }F,\ \exists R^\sharp\text{ on }F^\sharp\text{ and a coupling}:\quad \mathbb P\bigl(T_{WS}(F;X_0,R)\le T_{WS}(F^\sharp;Y_0,R^\sharp)\bigr)=1 .$$
--
--   Here a coupling is a probability measure on pairs of trajectories whose first marginal is the law of WalkSAT on $(F;X_0,R)$ and whose second marginal is the law of WalkSAT on $(F^\sharp;Y_0,R^\sharp)$. $F^\sharp$ has $m$ clauses and is in the opposite-sign case, so display (5) bounds the right-hand side.
--
--   Differences from the source:
--   - reading: an adaptive rule may depend on the history through time t but not on future random choices → a family of Markov kernels from the history (all past states, including the record of past choices) to a choice, possibly randomized; reason: the paper's uniform rule is randomized and is an instance of "every adaptive rule" in Theorems 3.1 and 3.4 (proof of Theorem 1.1, p. 11), so the class contains randomized rules; deterministic rules are the Dirac case
--   - encoding: a coupling with P(T_WS(F) ≤ T_WS(F♯)) = 1 → a measure P on pairs of trajectories whose two marginals (Measure.map Prod.fst / Prod.snd) are the two WalkSAT trajectory laws, and T_WS(F) ≤ T_WS(F♯) P-almost everywhere; reason: Lean convention; the marginal conditions make P a probability measure
--   - encoding: the running time T and its expectation → an ℕ∞-valued hitting time on trajectories of the Ionescu–Tulcea trajectory law, expectation as lintegral in ℝ≥0∞; reason: Lean convention; same quantity, with no integrability assumption
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), Proposition 3.3, p. 12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_WalkSAT
import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Split

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MTWalkSAT3CNF.TwoOcc

/-- Proposition 3.3 (same-sign splitting), p. 12: let `Δ(F) ≤ 2` and let `F♯` be obtained by
splitting every variable with two same-sign occurrences. For every initial assignment `X_0` and
every adaptive rule `R` on `F` there are an adaptive rule `R♯` on `F♯` and a coupling of WalkSAT
on `(F; X_0, R)` and on `(F♯; Y_0, R♯)` under which `T_WS(F; X_0, R) ≤ T_WS(F♯; Y_0, R♯)` with
probability one. -/
theorem proposition_3_3 {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ} (F : Formula V m)
    (hΔ : MaxOccLeTwo F) (X₀ : V → Bool) (R : WSRule F) :
    ∃ (R' : WSRule (splitFormula F))
      (P : Measure ((ℕ → WSState V m) × (ℕ → WSState (SplitVar F) m))),
      P.map Prod.fst = wsLaw F R (Measure.dirac X₀) ∧
      P.map Prod.snd = wsLaw (splitFormula F) R' (Measure.dirac (splitInit F X₀)) ∧
      ∀ᵐ ω ∂P, wsTimeOf F ω.1 ≤ wsTimeOf (splitFormula F) ω.2 := by sorry

end MTWalkSAT3CNF.TwoOcc
