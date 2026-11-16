-- Prove2me | Theorems.Thm_IPPComplexities_Unconditional_Supplement_theorem_1_2
-- name    : IPPComplexities.Unconditional.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:34:38.416427+00:00
-- url     : https://prove2.me/theorems/17a58bab-3974-4e90-9695-c3953dfe041a
-- title:
--   Theorem 1.2 — conditional lower bound for properties in E and NP
-- statement:
--   Suppose that the class $\mathsf E$ (resp. $\mathsf{NP}$) contains a set $S$ that is almost-everywhere hard for small-exponential circuits: for some constant $\alpha>0$ and all but finitely many $n$, every Boolean circuit of size at most $2^{\alpha n}$ with $n$ inputs errs on some $n$-bit string. Then there are a property $\Pi\in\mathsf E$ (resp. $\Pi\in\mathsf{NP}$) and a proximity parameter $\epsilon_0\in(0,1)$ such that every IPP for $\Pi$ at proximity $\epsilon_0$ satisfies
--
--   $$q(n)+c(n)=\Omega\!\left(\frac{n}{\log_2 n}\right).$$
--
--   Here an IPP is any nonuniform private-coin verifier system $V$ that is valid at proximity $\epsilon_0$ (members of $\Pi$ have a prover accepted with probability at least $2/3$; for strings $\epsilon_0$-far from $\Pi$, every prover is rejected with probability at least $2/3$), with no restriction on its computational complexity, its coins or its number of rounds. $q(n)$ and $c(n)$ are worst-case bounds on its number of queries and on the number of bits exchanged in both directions. The $\Omega$ means: there are $\kappa>0$ and $N\ge2$, depending on $V$, with $\kappa\, n/\log_2 n\le q(n)+c(n)$ for every $n\ge N$.
--
--   Both branches are stated: the E branch and the NP branch, each with $\Pi$ in the same class as $S$.
--
--   This brings the unconditional lower bound of Theorem 1.1 from double-exponential time down to E or NP, at the price of a circuit lower bound assumption.
--
--   **Formalization Note** $\epsilon_0$ is chosen before the verifier, as in the convention for lower bounds; $\kappa$ and $N$ after it. Membership in E and NP is decided by an actual time-bounded single-tape machine. The lower bound holds at every large length $n$, not only at lengths of a code.
--
--   Differences from the source:
--   - reading: S does not have circuit size 2^{αn} for some small constant α > 0 → for some α > 0 and all but finitely many n, every well-formed one-output circuit of size at most 2^{αn} with n inputs errs on some n-bit string; reason: the paper proves Theorem 1.2 as the special case C ∈ {E, NP} of Theorem 4.1, whose hypothesis is exactly this almost-everywhere hardness, and the eventual conclusion needs it
--   - encoding: circuit size → number of input wires plus fan-in-two gates over constants, ¬, ∧, ∨; reason: differs from the gate count by n ≤ 2^{αn}, so the hard sets are the same up to the choice of α
--   - encoding: the classes E and NP → single-tape deciders within 2^{C(n+1)} steps; a polynomial-time relation on an injective pairing with witnesses of length at most (|x|+1)^k; reason: the classes are robust to these standard models
--   - encoding: q(n) + c(n) = Ω(n/log n) at a sufficiently small constant proximity, for every IPP → one ε₀ ∈ (0,1) before the verifier, κ > 0 and N ≥ 2 after it, for every system valid at ε₀ with worst-case bounds q, c, in the published model; reason: the paper's convention for lower bounds, stated exactly as in the published Theorem 1.1
-- source:
--   Noga Amit, Oded Goldreich, STOC 2027 submission #297 (October 2026), p. 1, Theorem 1.2 (PDF p. 3); proof via Theorem 4.1, pp. 9–12 (PDF pp. 11–14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/297.pdf

import Definitions.Def_IPPComplexities_Unconditional_validity
import Definitions.Def_IPPComplexities_Unconditional_Supplement_classes

namespace IPPComplexities.Unconditional.Supplement

/-- Theorem 1.2, both branches: an almost-everywhere 2^{αn}-hard set in E (resp. NP)
yields a property in E (resp. NP) with the eventual Ω(n/log n) query-plus-communication
lower bound of Theorem 1.1, at one fixed proximity ε₀, against every valid nonuniform
private-coin system. -/
theorem theorem_1_2 :
    ((∃ S : Property, InE S ∧ AEHard S) →
        ∃ (L : Property) (ε₀ : ℝ), InE L ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
          ∀ (V : System) (q c : ℕ → ℕ),
            ValidAt L ε₀ V → ResourceBounds V q c →
            ∃ (κ : ℝ) (N : ℕ), 0 < κ ∧ 2 ≤ N ∧
              ∀ n : ℕ, N ≤ n →
                κ * ((n : ℝ) / Real.logb 2 (n : ℝ)) ≤ (q n + c n : ℕ)) ∧
      ((∃ S : Property, InNP S ∧ AEHard S) →
        ∃ (L : Property) (ε₀ : ℝ), InNP L ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
          ∀ (V : System) (q c : ℕ → ℕ),
            ValidAt L ε₀ V → ResourceBounds V q c →
            ∃ (κ : ℝ) (N : ℕ), 0 < κ ∧ 2 ≤ N ∧
              ∀ n : ℕ, N ≤ n →
                κ * ((n : ℝ) / Real.logb 2 (n : ℝ)) ≤ (q n + c n : ℕ)) := by sorry

end IPPComplexities.Unconditional.Supplement
