-- Prove2me | Theorems.Thm_KSATWindow_terminal_decomposition
-- name    : KSATWindow.terminal_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:42.592189+00:00
-- url     : https://prove2.me/theorems/240e5769-e5b4-4a20-a5b8-56dec5ff98b7
-- title:
--   Terminal decomposition and (1.2) — $\mathbb E\,r_n(\Gamma_n)=O_k(n^{2/k})$
-- statement:
--   Fix $k\ge3$. For every $n\ge k$, with $\Gamma_n=F_{n,T_n-1}$ the last satisfiable formula,
--
--   1. $\displaystyle\mathbb E\,r_n(\Gamma_n)=\sum_{m\ge0}\mathbb E\big[\mathbf 1\{T_n=m+1\}\,r_n(F_{n,m})\big]$;
--   2. $\displaystyle\sum_{m\ge0}\mathbb E\big[\mathbf 1\{T_n=m+1\}\,r_n(F_{n,m})\big]=\sum_{m\ge0}\mathbb E\big[\mathbf 1\{T_n>m\}\,\rho_k(F_{n,m})\,r_n(F_{n,m})\big]$;
--   3. $\displaystyle\mathbb E\,r_n(\Gamma_n)\le\frac{a_n^{1/k}}2\sum_{m\ge0}\mathbb E\Big[\mathbf 1\{T_n>m\}\frac{\ell(F_{n,m})}n\Big]$;
--   4. $\displaystyle\sum_{m\ge0}\mathbb E\Big[\mathbf 1\{T_n>m\}\frac{\ell(F_{n,m})}n\Big]=\int_0^\infty\beta_n(t)\,dt$;
--
--   and
--
--   5. there is $C$, depending only on $k$, with
--   $$\mathbb E\,r_n(\Gamma_n)\le C\,n^{2/k}\qquad\text{for every }n\ge k.\qquad(1.2)$$
--
--   The remaining expected time of the last satisfiable formula is small, although the clause that destroys it was selected by its success; with (4.1) this gives the variance bound.
--
--   Differences from the source:
--   - encoding: n ≥ k (and k ≥ 3, the standing assumption of §2) → hypotheses k ≤ n; reason: for n < k the set of clauses is empty and the clause law is not a probability measure; the paper's n → ∞ leaves small n unspecified
--   - encoding: a formula G (need not be a k-CNF) → its solution set S : Finset (Assignment n), satisfiable iff S ≠ ∅; reason: every quantity depends on G only through its solution set, and every set of assignments is a solution set
--   - encoding: 1{Tₙ > m}, 1{Tₙ = m+1} → F_{n,m} satisfiable; firstFailure = m + 1; reason: equal events
--   - reading: O_k(n^{2/k}) as n → ∞ → ∃ C, ∀ n ≥ k; reason: equivalent: E rₙ(Γₙ) ≤ aₙ < ∞ for each n, so finitely many n can be absorbed into C
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §4, p.8, proof of Theorem 1.3 (unnumbered displays), and eq. (1.2), p.3

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_KSATWindow_Window
import Definitions.Def_KSATWindow_Forcing
import Definitions.Def_KSATWindow_PoissonTime
open MeasureTheory ProbabilityTheory OAI.RandomKSAT
open scoped Classical ENNReal

namespace KSATWindow

/-- **Terminal decomposition and (1.2), p.8 (proof of Theorem 1.3) and p.3.** G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §4, p.8,
and (1.2), p.3.

Fix `k ≥ 3`. For every `n ≥ k`, with `Γₙ = F_{n,Tₙ−1}`,
1. `E rₙ(Γₙ) = Σ_{m≥0} E[1{Tₙ = m+1} rₙ(F_{n,m})]`;
2. `Σ_{m≥0} E[1{Tₙ = m+1} rₙ(F_{n,m})] = Σ_{m≥0} E[1{Tₙ > m} ρ_k(F_{n,m}) rₙ(F_{n,m})]`;
3. `E rₙ(Γₙ) ≤ (aₙ^{1/k}/2) Σ_{m≥0} E[1{Tₙ > m} ℓ(F_{n,m})/n]`;
4. `Σ_{m≥0} E[1{Tₙ > m} ℓ(F_{n,m})/n] = ∫₀^∞ βₙ(t) dt`;

and 5. `E rₙ(Γₙ) = O_k(n^{2/k})` (1.2): there is `C`, depending on `k` only, with
`E rₙ(Γₙ) ≤ C n^{2/k}` for every `n ≥ k`.

**Formalization Note.** All expectations and sums are in `[0, ∞]`. `1{Tₙ > m}` is
"`F_{n,m}` is satisfiable" and `1{Tₙ = m+1}` is `firstFailure ω = m + 1`. -/
theorem terminal_decomposition (k : ℕ) (hk : 3 ≤ k) :
    (∀ n : ℕ, k ≤ n →
      (∫⁻ ω, ENNReal.ofReal (lifetime n k (lastSatisfiable ω)) ∂(streamLaw n k) =
        ∑' m : ℕ, ∫⁻ ω, (if firstFailure ω = ((m + 1 : ℕ) : ℕ∞) then
          ENNReal.ofReal (lifetime n k (solutions ω m)) else 0) ∂(streamLaw n k)) ∧
      (∑' m : ℕ, ∫⁻ ω, (if firstFailure ω = ((m + 1 : ℕ) : ℕ∞) then
          ENNReal.ofReal (lifetime n k (solutions ω m)) else 0) ∂(streamLaw n k) =
        ∑' m : ℕ, ∫⁻ ω, (if (solutions ω m).Nonempty then
          ENNReal.ofReal (rho n k (solutions ω m) * lifetime n k (solutions ω m)) else 0)
            ∂(streamLaw n k)) ∧
      (∫⁻ ω, ENNReal.ofReal (lifetime n k (lastSatisfiable ω)) ∂(streamLaw n k) ≤
        ENNReal.ofReal (meanTime n k ^ ((1 : ℝ) / (k : ℝ)) / 2) *
          ∑' m : ℕ, ∫⁻ ω, (if (solutions ω m).Nonempty then
            ENNReal.ofReal ((forcedCount (solutions ω m) : ℝ) / (n : ℝ)) else 0)
              ∂(streamLaw n k)) ∧
      (∑' m : ℕ, ∫⁻ ω, (if (solutions ω m).Nonempty then
          ENNReal.ofReal ((forcedCount (solutions ω m) : ℝ) / (n : ℝ)) else 0) ∂(streamLaw n k) =
        ∫⁻ t in Set.Ioi (0 : ℝ), beta n k t)) ∧
    ∃ C : ℝ, ∀ n : ℕ, k ≤ n →
      ∫⁻ ω, ENNReal.ofReal (lifetime n k (lastSatisfiable ω)) ∂(streamLaw n k) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ ((2 : ℝ) / (k : ℝ))) := by sorry

end KSATWindow
