-- Prove2me | Theorems.Thm_FreeReplExchange_round_polytime
-- name    : FreeReplExchange.round_polytime
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:19:17.822231+00:00
-- url     : https://prove2.me/theorems/834433f6-4def-49c6-9708-4baa3796b288
-- title:
--   §5.4.1 — each round of M3 is polynomial time for rational utilities in binary
-- statement:
--   For rational utility parameters encoded in binary, one round of M3 — constructing $G_t$ from the state $(x^{(0)},U,P,x,D)$ and selecting the matching that maximizes $\Phi=(|\mu|,g(\mu),T(\mu))$ — can be computed by a deterministic Turing machine in time polynomial in the length of the binary encoding of the round input, hence polynomial in $n$, $m$ and the bit length of the utility parameters. The tie order is the lexicographic order by $(i,j,r,s)$.
--
--   This is the per-round time clause of Theorem 10; the paper derives it from Lemma 4 and a general-graph maximum-weight matching algorithm.
--
--   **Formalization Note** The machine model is Mathlib's multi-stack Turing machine with polynomial time bound, `Turing.TM2ComputableInPolyTime`, over the alphabet `Bool`. The output is the incidence vector of the proposal set over all quadruples $((i,r),(j,s))$.
--
--   Differences from the source:
--   - generalization: every good is initially held by at least one agent (WLOG, p.13) → any initial allocation x⁽⁰⁾; reason: no step of the proof uses the assumption; the source's instances are among those covered
--   - reading: each round takes time polynomial in n, m and the encoding length of the utility parameters (no machine model named) → Turing.TM2ComputableInPolyTime over Bool for the binary code encRoundInput of the round state, output the incidence vector of P_t; reason: the paper fixes the input model (rationals in binary); multi-stack Turing machines are a standard model, polynomially equivalent to the others, and the input length is polynomial in n, m and the utilities' bit length
--   - reading: the global tie order (any total order) → the paper's example order, lexicographic by (i, j, r, s) (lexRank); reason: a machine needs a concrete order; the paper names this one (p.32)
--   - generalization: the state of a round of M3 → any round input (n, m, x⁽⁰⁾, rational U with the sign conditions, P, x ≥ x⁽⁰⁾, D); reason: every round state is such an input, so the claim specializes to the rounds of M3; the sign conditions are the model's domain
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), p.38 (PDF p.40), §5.4.1, last paragraph; p.33 (PDF p.35), "Polynomial-time implementation"

import Mathlib
import Definitions.Def_FreeReplExchange_m3RoundQ

namespace FreeReplExchange

/-- §5.4.1, last paragraph, Yang–Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with
Negative Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…), p.38 (PDF p.40), with §4.2 "Polynomial-time
implementation", p.33: for rational utility parameters encoded in binary, one round of M3 (graph
construction and selection of the matching maximizing (18)) is computable in time polynomial in
`n`, `m` and the bit length of the utility parameters.

**Formalization Note.** Machine model: Mathlib's deterministic multi-stack Turing machines,
`Turing.TM2ComputableInPolyTime`, over the alphabet `Bool`. The input is the binary code
`encRoundInput` of the round state `(n, m, x^(0), U, P, x, D)` with rational `U` satisfying the sign
conditions and `x ≥ x^(0)`; its length is polynomial in `n`, `m` and the utilities' bit length
and at least `n²m`. The output is the incidence vector of the proposal set `P_t`. The tie order is
the paper's example, lexicographic in `(i, j, r, s)`. -/
theorem round_polytime :
    Nonempty (Turing.TM2ComputableInPolyTime encRoundInput (fun l : List Bool => l) m3RoundQ) := by sorry

end FreeReplExchange
