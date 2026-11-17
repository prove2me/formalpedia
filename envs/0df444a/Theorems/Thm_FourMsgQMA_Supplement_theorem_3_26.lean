-- Prove2me | Theorems.Thm_FourMsgQMA_Supplement_theorem_3_26
-- name    : FourMsgQMA.Supplement.theorem_3_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:31:18.658115+00:00
-- url     : https://prove2.me/theorems/438f2cd0-050d-4bb9-ae1d-4a608980076e
-- title:
--   Theorem 3.26 — guaranteed extraction for Kilian's argument [LMS22]
-- statement:
--   This is Theorem 3.26 (guaranteed extraction for Kilian's argument, after [LMS22]) in the pinned-down version requested by the operator.
--
--   Let $H$ be an efficient keyed hash family that is **collapsing** (Definition 3.12), let $R$ be an efficiently computable relation with polynomial declared bounds, and let $P$ be an efficient nonadaptive PCP for $R$ that is complete and has **full-proof knowledge error** $\kappa$ (Definition 3.24) for a negligible $\kappa$. Then Kilian's argument built from the balanced Merkle tree of $H$ over one-bit blocks and $P$ has **guaranteed extraction** (Definition 3.25) for $R$: there are a uniform witness-finding procedure, with coherent access to the prover's response circuit and its inverse and run on the one residual state $\rho_B$, and a polynomial $P_{\mathrm{time}}$ such that for every QPT prover $A$ with quantum advice
--   $$
--   \Pr\big[B=1\wedge R(u,w)\ne1:(u,B,w)\leftarrow\mathrm{GE}_A(1^\lambda)\big]\le\mathrm{negl}(\lambda),\qquad \mathbb E[\mathrm{Time}_{\mathrm{GE}}]\le P_{\mathrm{time}}(\lambda,M,T_A).
--   $$
--   Both bounds are over the whole experiment, not conditional on $(vk,u,\beta)$ or on $B=1$.
--
--   Guaranteed extraction is the hypothesis on Kilian's argument in Theorems 5.1 and 7.5; it lets a reduction recover the authorization witness from an accepting prover while preserving its state.
--
--   Differences from the source:
--   - reading: "Kilian's argument instantiated with a collapsing hash" → Kilian.mk H P with H efficient (§3.7 bounds) and collapsing; the Merkle commitment is the balanced tree of H of depth ⌈log₂ M⌉ with one key per level and domain-separated leaves (0‖index‖block) and nodes (1‖index‖children); reason: §3.8 (p.16) instantiates the commitment as balanced Merkle trees with domain separation but fixes no layout
--   - reading: "a PCP of knowledge with negligible knowledge error" → an efficiently computable relation R and a PCP P that is efficient (succinct verification), complete for R, and satisfies Definition 3.24 for a negligible κ; reason: §3.12 syntax and completeness (p.22); a relation is "a fixed, uniformly computable predicate … with declared … bounds" (p.22)
--   - reading: a quantum procedure FindWitness_A with coherent access to the response circuit and its inverse → one uniformly generated Extractor (gates H, S, T, X, CNOT on its own register and calls of U, U†), chosen before the prover (∃ procedure ∀ A), with classical input (vk, u, β, r, L_a); reason: black-box access as in [LMS22, Definition 8.1]; the procedure touches the prover only through U, U†; this is the stronger reading
--   - encoding: the response circuit run coherently, with measurement and random-coin registers retained (§3.5) → U = unitary dilation of round 1 of the IsQPT strategy: controlled on the seed register, the round-1 unitary on the core, then the self-delimiting answer XORed into an answer register of 2L_a+1 wires; the classical tape is sampled once; reason: §3.5 (p.14) convention; the paper fixes no circuit model
--   - encoding: E[Time_GE] ≤ P(λ, M, T_A) for a polynomial P → the expected total cost of the procedure's steps (1 per step and per gate, T_A = |A| + L_a per call of U or U†) in [0, ∞] is at most a four-variable ℕ-polynomial P(λ, M, T_A), for every polynomial bound L_a on the round-1 answer length; the fixed-cost stages are polynomial and absorbed in P; reason: the paper fixes no time measure; a step that never halts makes the expectation infinite
--   - encoding: every QPT A with the allowed auxiliary input; probability over the whole experiment → every published IsQPT strategy (round 0: vk ↦ (u, β), round 1: q ↦ a) with quantum advice; probabilities over the setup coins, the prover's tape, its round-0 outcome, the measurement of B and every internal outcome; reason: pinned-down model P2 of the base mission
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Theorem 3.26, p.23 (PDF 25); Definitions 3.12, 3.24, 3.25, pp.15–23

import Mathlib
import Definitions.Def_FourMsgQMA_Supplement_GuaranteedExtraction

namespace FourMsgQMA

namespace Supplement

open TightPQRepetition.Main

/-- **Theorem 3.26** (Guaranteed extraction for Kilian's argument [LMS22]), Goyal, Koppula, STOC 2027
submission (sha256 6c523d45…), p.23 (PDF 25): "Kilian's argument instantiated with a collapsing hash
and a PCP of knowledge with negligible knowledge error satisfies Definition 3.25."

For every efficient collapsing hash family `H` (§3.7, Definition 3.12), every efficiently computable
bounded relation `R`, and every efficient, complete nonadaptive PCP for `R` whose full-proof knowledge
error (Definition 3.24) is a negligible `κ`, Kilian's argument built from the balanced Merkle tree of
`H` over one-bit blocks and that PCP has guaranteed extraction (Definition 3.25) for `R`: a uniform
witness-finding procedure with coherent access to the prover's response circuit and its inverse, run
on the one residual state, fails (`B = 1 ∧ R(u, w) ≠ 1`) with negligible probability against every QPT
prover, and has expected running time at most `P(λ, M, T_A)` for one polynomial `P`.

**Formalization Note** Pinned-down version (operator request): the Merkle tree is the balanced tree
of `Supplement.merkleCommit` with one key per level; the procedure model and its time measure are
those of `Supplement.Kilian.GuaranteedExtraction`. -/
theorem theorem_3_26 (H : HashFamily) (hH : H.Efficient) (hcol : H.Collapsing)
    (R : Relation) (hR : R.Efficient) (P : PCP) (hP : P.Efficient) (hPc : P.Complete R)
    (κ : ℕ → ℝ) (hκ : Negligible κ) (hK : P.KnowledgeError R κ) :
    (Kilian.mk H P).GuaranteedExtraction R := by sorry

end Supplement

end FourMsgQMA
