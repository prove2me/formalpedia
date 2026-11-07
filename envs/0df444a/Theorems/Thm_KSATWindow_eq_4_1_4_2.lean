-- Prove2me | Theorems.Thm_KSATWindow_eq_4_1_4_2
-- name    : KSATWindow.eq_4_1_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:52.75247+00:00
-- url     : https://prove2.me/theorems/b05796b8-b80a-4dfd-b166-367e3193f2bd
-- title:
--   (4.1)–(4.2) — $\operatorname{Var}(T_n)\le\kappa a_n\mathbb E r_n(\Gamma_n)$ and $\rho_k r_n\le\min\{1,a_n\rho_k\}\le a_n^{1/k}\rho_k^{1/k}\le\frac{a_n^{1/k}}2\frac{\ell}{n}$
-- statement:
--   1. There is an absolute constant $\kappa$ such that for every $k\ge3$ and $n\ge k$,
--   $$\operatorname{Var}(T_n)\le\kappa\,a_n\,\mathbb E\,r_n(\Gamma_n),\qquad(4.1)$$
--   where $\Gamma_n=F_{n,T_n-1}$ is the last satisfiable formula of the process.
--   2. For every $k\ge3$, $n\ge k$ and every satisfiable formula $G$ on $[n]$,
--   $$\rho_k(G)\,r_n(G)\le\min\{1,a_n\rho_k(G)\}\le a_n^{1/k}\rho_k(G)^{1/k}\le\frac{a_n^{1/k}}{2}\,\frac{\ell(G)}{n}.\qquad(4.2)$$
--
--   (4.1) is Aldous's inequality for the clause process, whose last uncovered set is the solution set of $\Gamma_n$; (4.2) converts the hazard at the terminal state into a count of forced variables.
--
--   Differences from the source:
--   - encoding: n ≥ k (and k ≥ 3, the standing assumption of §2) → hypotheses k ≤ n; reason: for n < k the set of clauses is empty and the clause law is not a probability measure; the paper's n → ∞ leaves small n unspecified
--   - encoding: a formula G (need not be a k-CNF) → its solution set S : Finset (Assignment n), satisfiable iff S ≠ ∅; reason: every quantity depends on G only through its solution set, and every set of assignments is a solution set
--   - encoding: Var(Tₙ) → evariance of H in [0,∞]; reason: no junk value: the bound also asserts finiteness
--   - reading: the absolute constant κ of Theorem 4.1 → some absolute κ, the same for all k and n; reason: (4.1) is stated with the κ of Theorem 4.1, which is absolute
--   - reading: (4.2) introduced for G with ρₖ(G) > 0 → every satisfiable G; reason: the paper's last sentence: "The estimate therefore holds in all cases"
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §4, p.8, proof of Theorem 1.3, eqs. (4.1), (4.2)

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_KSATWindow_Window
import Definitions.Def_KSATWindow_Forcing
open MeasureTheory ProbabilityTheory OAI.RandomKSAT
open scoped Classical ENNReal

namespace KSATWindow

/-- **(4.1), (4.2), p.8 — Aldous's inequality for k-SAT and the terminal comparison.**
G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §4, proof of Theorem 1.3, p.8.

1. There is an absolute constant `κ` such that for every `k ≥ 3` and `n ≥ k`,
   `Var(Tₙ) ≤ κ aₙ E rₙ(Γₙ)` (4.1), where `Γₙ = F_{n,Tₙ−1}` is the last satisfiable formula.
2. For every `k ≥ 3`, `n ≥ k` and satisfiable `G` on `[n]` (solution set `S ≠ ∅`),
   `ρ_k(G) rₙ(G) ≤ min{1, aₙ ρ_k(G)} ≤ aₙ^{1/k} ρ_k(G)^{1/k} ≤ (aₙ^{1/k}/2) ℓ(G)/n` (4.2).

**Formalization Note.** `Var(Tₙ)` is `evariance H`, in `[0, ∞]`; `E rₙ(Γₙ)` is a lower integral.
`rₙ(G) = lifetime n k S`. -/
theorem eq_4_1_4_2 :
    (∃ κ : NNReal, ∀ k : ℕ, 3 ≤ k → ∀ n : ℕ, k ≤ n →
      evariance (H : Stream n k → ℝ) (streamLaw n k) ≤
        (κ : ℝ≥0∞) * ENNReal.ofReal (meanTime n k) *
          ∫⁻ ω, ENNReal.ofReal (lifetime n k (lastSatisfiable ω)) ∂(streamLaw n k)) ∧
    (∀ k : ℕ, 3 ≤ k → ∀ n : ℕ, k ≤ n → ∀ S : Finset (Assignment n), S.Nonempty →
      rho n k S * lifetime n k S ≤ min 1 (meanTime n k * rho n k S) ∧
      min 1 (meanTime n k * rho n k S) ≤
        meanTime n k ^ ((1 : ℝ) / (k : ℝ)) * rho n k S ^ ((1 : ℝ) / (k : ℝ)) ∧
      meanTime n k ^ ((1 : ℝ) / (k : ℝ)) * rho n k S ^ ((1 : ℝ) / (k : ℝ)) ≤
        meanTime n k ^ ((1 : ℝ) / (k : ℝ)) / 2 * ((forcedCount S : ℝ) / (n : ℝ))) := by sorry

end KSATWindow
