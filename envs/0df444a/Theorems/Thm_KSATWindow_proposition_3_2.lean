-- Prove2me | Theorems.Thm_KSATWindow_proposition_3_2
-- name    : KSATWindow.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:48.646645+00:00
-- url     : https://prove2.me/theorems/a2469a62-d985-4633-b076-b8630becfced
-- title:
--   Proposition 3.2 — $\int_0^\infty\beta_n(t)\,dt=O_k(n^{1/k})$
-- statement:
--   For fixed $k\ge3$ there is a constant $C$, depending only on $k$, such that for every $n\ge k$
--   $$\int_0^\infty\beta_n(t)\,dt\le C\,n^{1/k},$$
--   where $\beta_n(t)$ is the expected proportion of forced variables of the Poisson-time formula $F_n(t)$, counted only before unsatisfiability.
--
--   The expected total time for which a uniformly chosen variable is forced before unsatisfiability is $O_k(n^{1/k})$; this is one of the two factors $n^{1/k}$ in the variance bound.
--
--   Differences from the source:
--   - encoding: n ≥ k (and k ≥ 3, the standing assumption of §2) → hypotheses k ≤ n; reason: for n < k the set of clauses is empty and the clause law is not a probability measure; the paper's n → ∞ leaves small n unspecified
--   - encoding: E f(Fₙ(t)) for the Poisson-time formula Fₙ(t) = F_{n,Π_t} → the Poisson mixture Σ_m e^{−t}t^m/m!·E f(F_{n,m}) in [0,∞]; reason: this is what independence of Π_t and the clauses gives; every statement uses one time t only
--   - reading: O_k(n^{1/k}) as n → ∞ → ∃ C, ∀ n ≥ k, ∫₀^∞ βₙ ≤ C n^{1/k}; reason: equivalent: each integral is finite (at most aₙ, as the proof on p.8 notes), so finitely many n can be absorbed into C
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §3, pp.7–8, Proposition 3.2, eq. (3.5)

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

/-- **Proposition 3.2, p.7 — integrated forcing.** G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §3, pp.7–8.

For fixed `k ≥ 3`, `∫₀^∞ βₙ(t) dt = O_k(n^{1/k})` (3.5): there is `C`, depending on `k` only,
with `∫₀^∞ βₙ(t) dt ≤ C n^{1/k}` for every `n ≥ k`.

**Formalization Note.** `O_k` as `n → ∞` is stated for every `n ≥ k`; this is equivalent,
because each integral is finite (at most `aₙ`, as the proof on p.8 says). -/
theorem proposition_3_2 (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, ∀ n : ℕ, k ≤ n →
      ∫⁻ t in Set.Ioi (0 : ℝ), beta n k t ≤ ENNReal.ofReal (C * (n : ℝ) ^ ((1 : ℝ) / (k : ℝ))) := by sorry

end KSATWindow
