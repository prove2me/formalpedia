-- Prove2me | Theorems.Thm_FreshSig_Layered_theorem_3_3
-- name    : FreshSig.Layered.theorem_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:44:23.177464+00:00
-- url     : https://prove2.me/theorems/c81a6daa-c3b6-4b0a-9f11-a371725ee7f9
-- title:
--   Theorem 3.3 — SigComp is correct, refreshes in $t_N+d\,t_C$ rounds and is epoch-unforgeable; it is realised in $M^+$
-- statement:
--   Let $M^+$ satisfy Section 3.1: synchronous rounds with a common start $\tau_0$ (with $h_0$ the prefix just before it), a preparation phase in which the adversary may call every signing interface, any number of adaptive corruptions, and a nonce routine and a commitment routine meeting Definitions A.5 and A.9 with durations $t_N$ and $t_C$. Fix the parties $[n]$, a maximum depth $d\ge 0$ and a label $g$. Then:
--
--   1. SigComp is **correct** (Definition A.2, items 1–3 for every maximum depth, and item 4 in every execution of $M^+$);
--   2. its **refresh takes** $t_{ref}=t_N+d\,t_C$ rounds: every party correct through round $\tau_0+t_{ref}$ outputs well-formed lists in round $\tau_0+t_{ref}$;
--   3. it is **epoch-unforgeable** at every party that follows the protocol: if a correct $P_j$ accepts $\hat\sigma$ as a signature of origin $i$ on $m$ in the epoch, then $\hat\sigma$ contains an ideal signature $\langle x\rangle_i$ whose first issue is a signing call for $(i,m)$ with label $g$, at or after the start and no later than the acceptance — for every origin $i$, corrupted or exposed included;
--   4. the directed pairs with valid forwarding information are characterised as in Lemma 3.1: $X_j\sim_q X_k$ iff the commitment routine delivered from $P_k$ to $P_j$ in layer $q$;
--
--   and in particular SigComp is **realised** in $M^+$ with maximum depth $d$ and a refresh of $t_{ref}$ rounds (Definition A.4: completion within $t_{ref}$ rounds, correctness, forwarding between correct parties only when $X_j\sim_q X_k$, epoch unforgeability at every correct verifier):
--   $$\mathrm{SigComp}\ \text{realised in}\ M^+\ \text{with}\ d,\quad t_{ref}=t_N+d\,t_C .$$
--   This is the paper's first construction of epoch signatures, valid for every number of corruptions; it supplies the hypothesis of the synchronous compiler (Theorem 3.8).
--
--   Differences from the source:
--   - generalization: a model M+ satisfying Section 3.1: synchronous rounds with common start τ0, authentic possibly lossy channels, the corruption and exposure rules of A.3 with a preparation phase A0, and nonce and commitment routines satisfying Definitions A.5 and A.9 against every admissible adversary with precorruptions, durations tN and tC → every execution `tr` (rounds of finite event lists) with `SigComp.Sec31 n d g τ₀ tN tC tr`: the symbolic rules hold (`Admissible`), every party runs SigComp's refresh and verification while it is correct (`FollowsRefresh`, `FollowsVerification`), and the routines meet the guarantees of A.5 (freshness at every correct party, §2.4) and A.9 in that execution; no requirement on channels, any number of adaptive corruptions, and every signing interface callable by anyone at any time, before and after τ0; reason: every execution of such an M+ satisfies these conditions (its routines meet their guarantees against its adversary, and everything anyone handles is in the record and obeys the public rules), and the extra adversarial freedom only enlarges the class; the scheme's guarantees are local and use none of the restrictions dropped
--   - generalization: a public epoch label g → any term `g : Term`; reason: no clause uses publicity of g; a public label is one instance (for a label no correct party can compute, no correct party completes refresh, and the clauses about correct parties hold trivially)
--   - generalization: the term set T of Appendix A.1 (constants, atoms, tuples, signatures, roots, leaves, proofs) → `Term` with, in addition, `pid i` (party identities as public constants) and `ext k i x`, outputs of other protected interfaces such as the counter-bound signer of Example A.7, created only by `extCall` events; reason: covers nonce routines built on the counter-bound signer, which §3.1 names; with no `extCall` event the extra constructor never occurs
--   - generalization: Definition A.2 quantifies over lists and candidates in T (well-typed terms) → over all values of the inductive type `Term`, whose `root ℓ V` need not be well typed; reason: SigComp's algorithms check the types they rely on (`IsRoot`), so the clauses hold for raw terms and in particular for well-typed ones
--   - encoding: parties P1, …, Pn and coordinates 1, …, n → indices 0, …, n − 1 (`i < n`), coordinate j of a vector belonging to party j; reason: index shift
--   - encoding: ⊥ entries, proofs and outputs; Verify ∈ {0, 1} → `Option` (`none` = ⊥); verification as a proposition `verify …` (holds iff the output is 1); reason: Lean convention; same instances
--   - reading: every root and proof is tagged with its type and, where needed, its invocation (p. 62) → `root ℓ V` and `prf ℓ V j` carry the depth ℓ and the vector, not an invocation tag (the explicit-vector realisation of Example A.10); reason: SigComp never needs invocation tags; the depth typing and the containment of entries are kept
--   - encoding: σ̂ = (i, m, σ, U, W, G) → the tuple term `tup [pid i, m, σ, tup (U.map pid), tup W, tup G]`, parsed by `SigComp.parse`; reason: an epoch signature is a term (it contains its ideal signature as a structural subterm)
--   - encoding: an execution, its prefixes, the record K(h), occurrence before τ, events grouped into rounds → `Execution = ℕ → List Event`; positions `(round, index)` in lexicographic order; `record tr p` = all terms of the events strictly before p; occurs before round τ0 = `∈ Sub (record tr (τ₀, 0))`; reason: direct transcription; the record is cumulative by construction
--   - reading: Refresh: nonce routine, then layers ℓ = 1..d; refresh takes tref = tN + d·tC rounds → lockstep schedule: nonce routine invoked in round τ0, layer ℓ in round τ0 + tN + (ℓ − 1)·tC once the outputs it needs are available, output in round τ0 + tN + d·tC once all are available; "takes tref rounds" = every party correct through round τ0 + tref outputs in round τ0 + tref; reason: synchronous parties start the joint routines together and each routine is given its stated duration
--   - reading: a party that follows the protocol / follows refresh; a correct verifier → corruption is an event `corrupt i`; `CorrectAt tr τ₀ i p`: no execution-phase corruption of i up to p (preparation-phase corruption does not count); following refresh = correct up to the refresh output, or through round τ0 + tref where completion is claimed; reason: A.3: a party is correct up to an event if it followed the protocol throughout that prefix; uncorrupted parties run the protocol
--   - reading: an invoking party obtains a local output (Definitions A.5, A.9) → one output event per invocation at a correct party (`single_output`); reason: the routines' output is a single value per invocation
--   - reading: "well-formed Ri" (Definition A.2 item 1; not defined explicitly for SigComp) → `WellFormedR n d R`: R has d + 1 entries and every r^ℓ is a root of depth ℓ; reason: the reading suggested by p. 14; it is met by every refresh output and is the only property signing and verification use
--   - reading: Definition A.2 item 4: "in every admissible execution" → in every execution satisfying `SigComp.Sec31` (`RefreshCorrectIn`); reason: refresh correctness depends on the execution model; Lemma 3.1 places it in a model satisfying Section 3.1
--   - reading: "the commitment routine delivered from Pk to Pj in layer q" (v_{j,k} = v_k, p. 63) → `SigComp.Delivered tr τ₀ g q k j`: the layer-q output of the correct P_j has entry k equal to the layer-q input of the correct P_k; reason: direct transcription over events
--   - reading: "σ̂ is accepted by Pj as a signature of origin i on m in that epoch" → an event `accept j g i m σ̂ q` at a position where P_j is correct; a correct P_j accepts only after its refresh output and only what `SigComp.verify` accepts against that output; reason: acceptance is the verification call returning 1
--   - reading: Definition A.4 item 3: "between correct parties Pj and Pk" → P_j and P_k correct through round τ0 + tref, at their refresh outputs; reason: both parties are correct throughout refresh, when forwarding information is formed
-- source:
--   Lenzen, Loss, Shi, Fresh Signatures without Fresh Keys, STOC 2027 submission (manuscript sha256 ac05cb97…), p. 15, Theorem 3.3

import Mathlib
import Definitions.Def_FreshSig_Layered_Term
import Definitions.Def_FreshSig_Layered_Execution
import Definitions.Def_FreshSig_Layered_EpochScheme
import Definitions.Def_FreshSig_Layered_SigComp

namespace FreshSig.Layered

/-- **Theorem 3.3 (The signature scheme).** Let `M+` satisfy Section 3.1 (party set `[n]`,
maximum depth `d`, label `g`, common start round `τ₀`, nonce routine of duration `tN` and
commitment routine of duration `tC`). Then SigComp is correct (Definition A.2, items 1–3 for every
maximum depth, item 4 in every execution), its refresh takes `tref = tN + d tC` rounds (every
party correct through round `τ₀ + tref` outputs well-formed lists in round `τ₀ + tref`), and it is
epoch-unforgeable (Definition A.3) at every party that follows the protocol; the directed pairs
with valid forwarding information are those of Lemma 3.1. In particular SigComp is realised in
`M+` with maximum depth `d` and a refresh of `tref` rounds (Definition A.4). -/
theorem theorem_3_3 (n d : ℕ) (g : Term) (τ₀ tN tC : ℕ) :
    (sigComp n).CorrectA2 n ∧
    (∀ tr : Execution, SigComp.Sec31 n d g τ₀ tN tC tr →
      (sigComp n).RefreshCorrectIn n d g τ₀ tr ∧
      (∀ i < n, CorrectThrough tr τ₀ i (τ₀ + SigComp.tref tN tC d) →
        ∃ (p : Pos) (R : List Term) (A : List FwdRecord), p.1 = τ₀ + SigComp.tref tN tC d ∧
          evAt tr p = some (Event.refreshOut i g R A) ∧ (sigComp n).wellFormedLists d R A) ∧
      (∀ j < n, (sigComp n).EpochUnforgeableAt d g τ₀ tr j) ∧
      (∀ j < n, ∀ k < n, ∀ (pj pk : Pos) (Rj Rk : List Term) (Aj Ak : List FwdRecord),
        CorrectAt tr τ₀ j pj → evAt tr pj = some (Event.refreshOut j g Rj Aj) →
        CorrectAt tr τ₀ k pk → evAt tr pk = some (Event.refreshOut k g Rk Ak) →
        ∀ q : ℕ, 1 ≤ q → q ≤ d →
          ((sigComp n).Compat Rj Aj q k Rk ↔ SigComp.Delivered tr τ₀ g q k j))) ∧
    (sigComp n).Realised n (SigComp.Sec31 n d g τ₀ tN tC) d g τ₀ (SigComp.tref tN tC d) := by sorry

end FreshSig.Layered
