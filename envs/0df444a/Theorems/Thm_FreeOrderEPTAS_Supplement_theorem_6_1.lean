-- Prove2me | Theorems.Thm_FreeOrderEPTAS_Supplement_theorem_6_1
-- name    : FreeOrderEPTAS.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:42:31.385046+00:00
-- url     : https://prove2.me/theorems/9047646f-4606-4f75-909d-f7e4ed35ae71
-- title:
--   Theorem 6.1 — an $\alpha$-approximation oracle for Free-Order Prophets gives a polynomial-time $\alpha$-approximation for Pandora's Box with Commitment
-- statement:
--   There are universal constants $C$ and $d$ with the following property. Let $\alpha\ge0$, let $(X,c)$ be an instance of Pandora's Box with Commitment with $n$ boxes, and let $A$ be an oracle for Free-Order Prophets that, given the oracle $v\mapsto\mathbb E[\max\{Z_i,v\}]$ of any instance $Z$ with $n$ variables, returns a permutation $\sigma$ with
--   $$V_Z(\sigma)\ \ge\ \alpha\cdot\mathrm{OPT}(Z).$$
--   Then the reduction (build $Y_i=\min\{X_i,\kappa_i\}$, call $A$ once on it, convert its permutation as in Claim 6.3), which accesses $X$ only through the oracle $\mathbb E[\max\{X_i,v\}]$ and reads Weitzman's indices, returns on every outcome a solution of Pandora's Box with Commitment with
--   $$\mathbb E\Big[X_{\sigma'(\tau')}-\sum_{t\le\tau'}c_{\sigma'(t)}\Big]\ \ge\ \alpha\cdot\mathrm{OPT}(X,c),$$
--   at a counted cost of at most $C\cdot(n+1)^d$, the call to $A$ counting as one step.
--
--   Together with Theorem 3.1 this yields the EPTAS of Theorem 1.4.
--
--   **Formalization Note** The cost model is the base mission's: unit-cost real operations and one count per oracle query. The oracle $A$ is a program in the base cost monad whose every outcome satisfies the guarantee; the reduction runs it from fresh counters and charges one unit. For $\alpha>1$ no such oracle exists once some instance has positive optimum, so the statement is about $0\le\alpha\le1$ in substance.
--
--   Differences from the source:
--   - reading: polynomial time → counted cost ≤ C·(n + 1)^d with C and d universal, in the base mission's unit-cost real-RAM model with counted oracle queries; reason: the cost model of the published goal (paper.md item 6)
--   - reading: oracle access to an α-approximation for Free-Order Prophets → a program A that, on the oracle E[max{Z_i, v}] of every Free-Order Prophets instance Z with n variables, returns on every outcome a permutation σ with α·OPT(Z) ≤ V_Z(σ); the reduction calls it exactly once, charged one unit, its internal work discarded; reason: an oracle answers in one step; its input is the instance Y given through its own oracle, as in Theorem 3.1
--   - generalization: an α-approximation for Free-Order Prophets on all instances → the guarantee is required only on instances with n variables, the size of the given instance; reason: a weaker hypothesis; an α-approximation on all instances satisfies it
--   - reading: κ_i, "the unique solution to E[(X_i − κ_i)^+] = c_i", with no method of computing it → the program receives κ as an input and reads κ_i at one counted operation per access; reason: κ_i is not exactly computable from E[max{X_i, v}] in finitely many real operations; the paper treats it as available
--   - encoding: Y_i = min{X_i, κ_i} → Y_i = max{min{X_i, κ_i}, 0}, and Y_i = X_i for κ_i = ∞; reason: the base instance requires non-negative values; the clip changes Y_i only when κ_i < 0 (c_i > E[X_i]), where Y_i is a.s. the constant κ_i < 0 resp. 0, and neither ever raises a stopping value
--   - reading: a solution is a probing permutation σ and a stopping rule τ (p.30), and the proofs of Claims 6.2–6.3 skip boxes the policy does not probe → a solution is either the empty solution (probe no box, utility 0) or a pair (σ, τ); a rule that never stops selects nothing and pays all n costs; reason: skipping every box must be a solution: if the only solutions were pairs (σ, τ), each probes at least one box, and for n = 1, X_1 = 0, c_1 = 1 every solution has utility −1 while V_Y(σ) = 0, so Claim 6.3 would be false and Theorem 6.1 false for α < 1
--   - generalization: all random variables are continuous (footnote 1, p.31, an assumption of the proof) → every non-negative integrable law; reason: κ_i exists and is unique for every integrable law with c_i > 0, and the per-box identities of both claims need no continuity; the continuous case is a special case
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Theorem 6.1, p.31 (proof pp.31–32)

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Supplement_pandoraReduce
import Definitions.Def_FreeOrderEPTAS_OPT
import Definitions.Def_FreeOrderEPTAS_orc

namespace FreeOrderEPTAS.Supplement

/-- Theorem 6.1 (arXiv:2007.13121v3, p.31): given oracle access to an `α`-approximation for
Free-Order Prophets, there is a polynomial-time `α`-approximation for Pandora's Box with Commitment.

For universal constants `C` and `d`: for every `α ≥ 0`, every instance `(X, c)` with `n` boxes and
every oracle `A` that, on the oracle `E[max{Z_i, v}]` of any Free-Order Prophets instance `Z` with `n` variables,
returns (on every outcome) a permutation `σ` with `α · OPT(Z) ≤ V_Z(σ)`, every outcome of the
reduction `pandoraReduce` — which reaches `X` only through its counted oracle, reads `κ`, and calls
`A` exactly once (charged one unit) — is a solution with expected utility at least
`α · OPT(X, c)`, at a counted cost of at most `C · (n + 1)^d`. -/
theorem theorem_6_1 :
    ∃ C d : ℕ, ∀ (α : ℝ), 0 ≤ α → ∀ (n : ℕ) (P : PandoraInstance n)
      (A : (Fin n → ℝ → ℝ) → Prog (Equiv.Perm (Fin n))),
      (∀ (Z : Instance n), ∀ r ∈ ((A (orc Z)).run 0).support, α * OPT Z ≤ V Z r.1) →
      ∀ r ∈ ((pandoraReduce (oracleCall A) (orc P.X) (kappa P) P.c).run 0).support,
        α * pandoraOPT P ≤ pandoraValue P r.1 ∧ r.2.total ≤ C * (n + 1) ^ d := by sorry

end FreeOrderEPTAS.Supplement
