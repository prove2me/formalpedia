-- Prove2me | Theorems.Thm_MinCostMaj_theorem_1_1
-- name    : MinCostMaj.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:35:38.610969+00:00
-- url     : https://prove2.me/theorems/0f064301-8df0-458b-a1ee-8266ff4e2551
-- title:
--   Theorem 1.1 — constant-factor approximation of $\mathrm{MinCostCSP}(\mathbf A)$ or a reduction from $\mathrm{cUG}(k)$
-- statement:
--   Let $\mathbf A$ be a finite relational structure admitting a conservative majority polymorphism. Then one of the following holds:
--
--   1. $\mathrm{MinCostCSP}(\mathbf A)$ admits a randomized polynomial-time constant-factor approximation algorithm: there are $C\ge1$ and a polynomial-time algorithm reading the instance and a polynomial number of random coins that, on every instance and every coin string, returns a solution when one exists (and reports infeasibility otherwise), with expected cost at most $C\cdot\mathrm{OPT}$;
--   2. a fixed-alphabet cyclic Unique Games deletion problem reduces to $\mathrm{MinCostCSP}(\mathbf A)$: for some $k\ge2$, weighted $\mathrm{cUG}(k)$ has a polynomial-time approximation-preserving reduction to $\mathrm{MinCostCSP}(\mathbf A)$.
--
--   Costs are in $\mathbb Q_{\ge0}\cup\{\infty\}$, the structure has any finite domain and any finite list of relations of any arities. Assuming the Unique Games Conjecture, $\mathrm{cUG}(k)$ has no constant-factor approximation, so the theorem is a dichotomy for constant-factor approximability.
--
--   Differences from the source:
--   - reading: MinCostCSP(A) admits a randomized polynomial-time constant-factor approximation algorithm → HasConstApprox A: ∃ C ≥ 1, a coin-length polynomial p and a TM2 polynomial-time machine on (instance, coin string) that on every coin string of length p(|enc I|) outputs a solution when one exists and "infeasible" otherwise, with uniform-coin average cost ≤ C·OPT; reason: the paper names no machine model; the guarantee is in expectation (Proposition 5.3) and the algorithm always returns a solution (Proposition 5.4)
--   - reading: a fixed-alphabet cyclic Unique Games deletion problem reduces to MinCostCSP(A) → ∃ k ≥ 2, CUGReducesTo k A: TM2 polynomial-time Φ, Ψ and a constant c with ΦG well formed with a finite-cost solution, OPT(ΦG) ≤ c·OPT(G), and cost_G(Ψ(G, α)) ≤ c·cost(α) for every solution α; arcs carry positive rational weights; reason: this is the approximation-preserving reduction of §4.1; positive weights contain unit weights (footnote 2)
--   - encoding: finite domain A, instances (V, C, {c_x}) with costs in Q≥0 ∪ {∞} → domain Fin d; instances as finite lists with `WellFormed`, ∞ as `none`, costs read into ℝ≥0∞; reason: same instances
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Theorem 1.1, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_MinCostMaj_Struct
import Definitions.Def_MinCostMaj_HasConsMajPol
import Definitions.Def_MinCostMaj_HasConstApprox
import Definitions.Def_MinCostMaj_CUGReducesTo

namespace MinCostMaj

/-- **Theorem 1.1 (main result)**, p.4 (PDF p.5).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Theorem 1.1, p.4: "Let A be a finite relational structure admitting a conservative majority
polymorphism. Then one of the following holds:
• MinCostCSP(A) admits a randomized polynomial-time constant-factor approximation algorithm;
• a fixed-alphabet cyclic Unique Games deletion problem reduces to MinCostCSP(A)."

For every finite relational structure `A` (domain `Fin d`, any finite list of relations of any
arities) with a conservative majority polymorphism: either there are `C ≥ 1`, a coin-length
polynomial and a polynomial-time machine that, on every well-formed MinCostCSP(A) instance (costs in
`ℚ≥0 ∪ {∞}`) and every coin string, outputs a solution when one exists and "infeasible" otherwise,
with expected cost at most `C · OPT`; or for some fixed `k ≥ 2` the weighted cUG(k) problem has a
polynomial-time approximation-preserving reduction to MinCostCSP(A).

**Formalization Note.** Machines are Mathlib's `Turing.TM2ComputableInPolyTime` on fixed binary
encodings; see `HasConstApprox` and `CUGReducesTo`. `k` depends only on `A` ("fixed-alphabet"). -/
theorem theorem_1_1 (d : ℕ) (A : Struct d) (hA : HasConsMajPol A) :
    HasConstApprox A ∨ ∃ k : ℕ, 2 ≤ k ∧ CUGReducesTo k A := by sorry

end MinCostMaj
