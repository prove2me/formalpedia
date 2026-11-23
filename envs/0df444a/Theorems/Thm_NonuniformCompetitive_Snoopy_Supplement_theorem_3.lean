-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_Supplement_theorem_3
-- name    : NonuniformCompetitive.Snoopy.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:01:41.319032+00:00
-- url     : https://prove2.me/theorems/20652c88-ba07-4bc1-afe1-d8718dd6fce0
-- title:
--   Theorem 3 — all-algorithm lower bound from the infimum of phase LP bounds
-- statement:
--   Let $T$ be a finite directed task system with initial state $s_0$ and the bounded phase property of §2. Its retained inputs have a finite alphabet of reachable phases, each beginning and ending at known optimal states with the stated forcing witnesses and with positive finite optimal cost; an unfinished final phase extends a complete one. Let $\mathcal B$ be the set of attained LP bounds over all causal randomized phase policies, initialized at the start of each phase and agreeing almost surely with its designated endpoint. Suppose $\alpha\in\mathbb R$ is the greatest lower bound of $\mathcal B$. Every randomized causal algorithm $A$, including algorithms that are not phase-based, satisfies
--   $$\bigl[\exists a\in\mathbb R\ \forall\sigma:\ \mathbb E C_A(\sigma)\le c C_{\rm opt}(\sigma)+a\bigr]\ \Longrightarrow\ \alpha\le c.$$
--   The input quantifier ranges over finite words with finite offline optimum. Local phase policies range over all causal policies on the retained phase-prefix domain; extending them through deleted requests is not a constraint of this LP. The infimum and each LP minimum are specified relationally, so empty or unbounded optimization sets do not receive a default real value.
--
--   This is the lower-bound counterpart of Theorem 2. The competitor is unrestricted apart from being a genuine measurable randomized causal algorithm; neither normalization nor a phase-policy reduction is assumed.
--
--   Differences from the source:
--   - encoding: the full bounded phase property of §2 → finite reachable phase alphabet, actual work-function known boundaries, endpoint forcing witnesses and incomplete-prefix extension; reason: these are the governing conditions on p.547; no all-state forcing premise is imposed
--   - encoding: the infimum of LP bounds for phase-based algorithms → IsGLB of attained LP minima over every initialized causal local phase policy with almost-sure endpoint synchronization; reason: the LP is defined on retained phases; requiring a global extension through excluded requests would add constraints absent on p.547
--   - encoding: no algorithm is competitive within a factor less than α → for every mixed causal algorithm A and real c, A.Competitive s₀ c implies α ≤ c; reason: the conclusion includes all algorithms and retains the one additive constant uniform over finite feasible input words
--   - reading: the phase proof uses known-state warm-up prefixes → phase starts are reachable after real input prefixes whose work function has that canonical known state; reason: the pp.548–549 argument needs actual algorithm histories; normalization and a reduction to phase policies are not hypotheses
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, pp. 548–549, Theorem 3; governing phase property p. 547

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_phaseSystem

namespace NonuniformCompetitive.Snoopy.Supplement

/-- Theorem 3, pp.548–549, with the full bounded phase property of p.547.
The LP bounds range over every causal mixed policy on retained phase words,
with initialization at the phase start and almost-sure endpoint agreement.
There is no requirement that such a policy extend transparently across deleted
requests, and no restriction of the competitor to normalized or phase policies.
Reachable phase boundaries are known states of the actual work function, so the
source warm-up prefixes are real task inputs. The infimum is a real greatest
lower bound; an empty or unbounded set is not assigned a default value.
The additive constant is kept inside Competitive, before every input word. -/
theorem theorem_3 {S R : Type} [Fintype S] [Fintype R] [LinearOrder S]
    (T : TaskSystem S R) (s₀ : S) (F : PhaseSystem T s₀) (hF : F.Valid)
    (α : ℝ) (hα : IsGLB (phaseBounds F) α) :
    ∀ (A : TaskRandomized T) (c : ℝ), A.Competitive s₀ c → α ≤ c := by sorry

end NonuniformCompetitive.Snoopy.Supplement
