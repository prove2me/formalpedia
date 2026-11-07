-- Prove2me | Theorems.Thm_KSATWindow_eq_3_2
-- name    : KSATWindow.eq_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:39.013241+00:00
-- url     : https://prove2.me/theorems/3a432a27-e95c-44d5-abc6-dc578af4ec27
-- title:
--   (3.2) — Poisson occupation identity $\int_0^\infty\mathbb E f(F_n(t))\,dt=\sum_{m\ge0}\mathbb E f(F_{n,m})$
-- statement:
--   Fix $k\ge3$ and $n\ge k$. For every nonnegative function $f$ of the formula,
--   $$\int_0^\infty\mathbb E\big[f(F_n(t))\big]\,dt=\sum_{m\ge0}\mathbb E\big[f(F_{n,m})\big],$$
--   as an identity in $[0,\infty]$; either side may be infinite.
--
--   Poisson time preserves the discrete occupation sums exactly, which lets the paper move between the clause count and continuous time.
--
--   Differences from the source:
--   - encoding: n ≥ k (and k ≥ 3, the standing assumption of §2) → hypotheses k ≤ n; reason: for n < k the set of clauses is empty and the clause law is not a probability measure; the paper's n → ∞ leaves small n unspecified
--   - encoding: a nonnegative function f of the formula F_{n,m} = C₁ ∧ ⋯ ∧ C_m → a function f m of its clause list (C₁, …, C_m) : Fin m → Clause n k; reason: the formula is its list of clauses, so this covers every function of the formula, in particular every function of its solution set
--   - encoding: E f(Fₙ(t)) for the Poisson-time formula Fₙ(t) = F_{n,Π_t} → the Poisson mixture Σ_m e^{−t}t^m/m!·E f(F_{n,m}) in [0,∞]; reason: this is what independence of Π_t and the clauses gives; every statement uses one time t only
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §3, p.7, eq. (3.2)

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_KSATWindow_Forcing
import Definitions.Def_KSATWindow_PoissonTime
open MeasureTheory ProbabilityTheory OAI.RandomKSAT
open scoped Classical ENNReal

namespace KSATWindow

/-- **(3.2), p.7 — Poisson occupation identity.** G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §3, p.7.

For `k ≥ 3`, `n ≥ k` and every nonnegative function `f` of the formula,
`∫₀^∞ E[f(Fₙ(t))] dt = Σ_{m≥0} E[f(F_{n,m})]` (3.2), in `[0, ∞]` (either side may be infinite).

**Formalization Note.** The formula `F_{n,m} = C₁ ∧ ⋯ ∧ C_m` is its list of clauses
`(ω 0, …, ω (m-1)) : Fin m → Clause n k`, so `f m` is an arbitrary nonnegative function of a
formula with `m` clauses (a function of the solution set is a special case). `E[f(Fₙ(t))]`,
with `Fₙ(t) = F_{n,Π_t}` and `Π_t` independent of the clauses, is the Poisson mixture
`Σ_m e^{-t} t^m / m! · E[f(F_{n,m})]`, the same encoding as `poissonMean` (definition module
`PoissonTime`). -/
theorem eq_3_2 (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n)
    (f : (m : ℕ) → (Fin m → Clause n k) → ℝ≥0∞) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ∑' m : ℕ, ENNReal.ofReal (poissonWeight t m) *
        ∫⁻ ω, f m (fun i : Fin m => ω i) ∂(streamLaw n k) =
      ∑' m : ℕ, ∫⁻ ω, f m (fun i : Fin m => ω i) ∂(streamLaw n k) := by sorry

end KSATWindow
