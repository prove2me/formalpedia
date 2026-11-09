-- Prove2me | Theorems.Thm_MinCostMaj_theorem_3_2
-- name    : MinCostMaj.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:35:53.984245+00:00
-- url     : https://prove2.me/theorems/cd6b5482-71a5-4dce-af10-1495ad2d962d
-- title:
--   Theorem 3.2 — the combinatorial dichotomy
-- statement:
--   Let $\mathbf A$ be a finite relational structure admitting a conservative majority polymorphism. Exactly one of the following holds:
--
--   1. there is an ac-leq-cycle pair $(I,J)$ such that $I$ has no solution; in this case, for some fixed $k\ge2$, weighted $\mathrm{cUG}(k)$ reduces to $\mathrm{MinCostCSP}(\mathbf A)$;
--   2. for every ac-leq-cycle pair $(I,J)$ the instance $I$ has a solution; in this case $\mathrm{MinCostCSP}(\mathbf A)$ admits a randomized polynomial-time constant-factor approximation algorithm.
--
--   The pairs range over instances on finite variable sets over the normalized structure of §3 (binary relations pp-definable from $\mathbf A$ and all unary relations). The condition is combinatorial, and §3.1 shows that no term condition on polymorphisms can replace it.
--
--   Differences from the source:
--   - encoding: exactly one of the following holds → (HardCond A → reduction) ∧ (TractCond A → approximation), with TractCond the negation of HardCond; reason: the two conditions are complementary, so exactly one holds
--   - reading: ac-leq-cycle pairs (I, J) of instances of CSP(A) → pairs of instances on Fin n over the normalized structure (`normBin A`), both following the opposite-readings convention; reason: §3 replaces A by the normalized structure before stating the condition; instances are finite
--   - reading: MinCostCSP(A) admits a randomized polynomial-time constant-factor approximation algorithm → HasConstApprox A: Turing-machine polynomial time on (instance, coin string), a solution on every coin string when one exists and "infeasible" otherwise, expected cost ≤ C·OPT; reason: the paper names no machine model; the guarantee is in expectation (Proposition 5.3) and the algorithm always returns a solution (Proposition 5.4)
--   - reading: a fixed-alphabet cyclic Unique Games deletion problem reduces to MinCostCSP(A) → ∃ k ≥ 2, CUGReducesTo k A: polynomial-time Φ, Ψ and a constant c with OPT(ΦG) ≤ c·OPT(G) and cost_G(Ψ(α)) ≤ c·cost(α), for positive rational arc weights; reason: this is the approximation-preserving reduction of §4.1; positive weights contain unit weights (footnote 2)
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Theorem 3.2, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MinCostMaj_Struct
import Definitions.Def_MinCostMaj_HasConsMajPol
import Definitions.Def_MinCostMaj_normBin
import Definitions.Def_MinCostMaj_HasConstApprox
import Definitions.Def_MinCostMaj_CUGReducesTo

namespace MinCostMaj

/-- **Theorem 3.2**, p.6 (PDF p.7).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Theorem 3.2, p.6: "Let A be a finite relational structure admitting a conservative majority
polymorphism. Then exactly one of the following holds:
• there exists an ac-leq-cycle pair (I, J) such that I has no solution; in this case a fixed-alphabet
cyclic Unique Games deletion problem reduces to MinCostCSP(A);
• for every ac-leq-cycle pair (I, J), the instance I has a solution; in this case MinCostCSP(A)
admits a randomized polynomial-time constant-factor approximation algorithm."

**Formalization Note.** The two conditions are `HardCond A` and `TractCond A` (instances over the
normalized structure of §3 on finite variable sets `Fin n`); they are each other's negation, which
is the "exactly one". MinCostCSP in both bullets is that of the given structure `A`. "Reduces" and
"randomized polynomial-time constant-factor approximation" are `CUGReducesTo` and
`HasConstApprox`. -/
theorem theorem_3_2 {d : ℕ} (A : Struct d) (hA : HasConsMajPol A) :
    (HardCond A → ∃ k : ℕ, 2 ≤ k ∧ CUGReducesTo k A) ∧
    (TractCond A → HasConstApprox A) := by sorry

end MinCostMaj
