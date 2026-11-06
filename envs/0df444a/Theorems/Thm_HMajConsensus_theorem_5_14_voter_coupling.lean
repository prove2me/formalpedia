-- Prove2me | Theorems.Thm_HMajConsensus_theorem_5_14_voter_coupling
-- name    : HMajConsensus.theorem_5_14_voter_coupling
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:51.613104+00:00
-- url     : https://prove2.me/theorems/a3e53db4-2506-4e49-bafb-b4f4ec77c4af
-- title:
--   Theorem 5.14 — coupling of $h$-Majority and Voter with $p^{(h)}(t)\succeq p^{(1)}(t)$ for all $t$
-- statement:
--   Let $h\ge2$. Consider $h$-Majority and Voter on the same $n$ nodes with opinion set $[k]$ ($2\le k\le n$), and write $p^{(h)}(t)$ and $p^{(1)}(t)$ for their empirical opinion distributions at round $t$. Suppose the initial distributions satisfy $p^{(h)}(0)\succeq p^{(1)}(0)$. Then there exists a coupling of the two processes, with their correct marginal laws, such that
--   $$\Pr\big[p^{(h)}(t)\succeq p^{(1)}(t)\ \text{for every integer }t\ge0\big]=1.$$
--   In particular, this holds when the two processes start from the same configuration.
--
--   Through this coupling, any bound on how quickly Voter loses opinions transfers to $h$-Majority (Corollary 5.21).
--
--   **Formalization Note** The two processes are the density paths $t\mapsto p(C(t))\in\mathbb R^k$ of $h$-Majority from $C_0$ and of Voter ($1$-Majority) from $C_1$; a coupling is a probability measure on pairs of density paths whose marginals are these two laws. The first conjunct is the theorem for $p(C_0)\succeq p(C_1)$, the second the "in particular" clause $C_1=C_0$. $\succeq$ is `AgriSubsidy.Combined.Majorizes`.
--
--   Differences from the source:
--   - encoding: a coupling of the two processes p^(h)(t), p^(1)(t) with correct marginal laws → a probability measure on pairs of density paths (ℕ → Fin k → ℝ)² whose marginals are the images of pathLaw h C₀ and pathLaw 1 C₁; the event holds almost surely; reason: the processes of the statement are the empirical distributions (p.25); same instances
--   - encoding: h-Majority as a sequence of random configurations (§2) → path law pathLaw h C₀ of the Markov kernel step h (product over nodes of Maj of h iid samples from p(C), uniform tie-breaking); reason: the §2 rule written as a kernel; the published Ionescu-Tulcea chain law gives the process
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Theorem 5.14, p.25 (the two processes p^(h)(t), p^(1)(t), p.25)

import Mathlib
import Definitions.Def_HMajConsensus_pathLaw
import Definitions.Def_AgriSubsidy_Combined_Majorization

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Theorem 5.14** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §5.2, p.25): let `h ≥ 2` and let the initial empirical distributions
satisfy `p^{(h)}(0) ⪰ p^{(1)}(0)`. There is a coupling of `h`-Majority and Voter on the same
`n` nodes, with their correct marginal laws, such that
`Pr[p^{(h)}(t) ⪰ p^{(1)}(t) for every integer t ≥ 0] = 1`. In particular, this holds when the two
processes start from the same configuration.

**Formalization Note** The two processes are the density paths `t ↦ p(C(t))` (vectors in
`Fin k → ℝ`) of `pathLaw h C₀` and of Voter `pathLaw 1 C₁`; a coupling is a probability measure
on pairs of density paths with these two marginals. The second conjunct is the "in particular"
clause (`C₁ = C₀`, no hypothesis). -/
theorem theorem_5_14_voter_coupling (n k h : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (hh : 2 ≤ h) :
    (∀ C₀ C₁ : Config n k,
      AgriSubsidy.Combined.Majorizes (density C₀) (density C₁) →
      ∃ μ : Measure ((ℕ → Fin k → ℝ) × (ℕ → Fin k → ℝ)), IsProbabilityMeasure μ ∧
        μ.map Prod.fst = (pathLaw h C₀).map (fun ω t => density (ω t)) ∧
        μ.map Prod.snd = (pathLaw 1 C₁).map (fun ω t => density (ω t)) ∧
        ∀ᵐ x ∂μ, ∀ t : ℕ, AgriSubsidy.Combined.Majorizes (x.1 t) (x.2 t)) ∧
    (∀ C₀ : Config n k,
      ∃ μ : Measure ((ℕ → Fin k → ℝ) × (ℕ → Fin k → ℝ)), IsProbabilityMeasure μ ∧
        μ.map Prod.fst = (pathLaw h C₀).map (fun ω t => density (ω t)) ∧
        μ.map Prod.snd = (pathLaw 1 C₀).map (fun ω t => density (ω t)) ∧
        ∀ᵐ x ∂μ, ∀ t : ℕ, AgriSubsidy.Combined.Majorizes (x.1 t) (x.2 t)) := by sorry

end HMajConsensus
