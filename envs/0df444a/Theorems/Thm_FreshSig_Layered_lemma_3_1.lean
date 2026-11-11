-- Prove2me | Theorems.Thm_FreshSig_Layered_lemma_3_1
-- name    : FreshSig.Layered.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:44:12.086275+00:00
-- url     : https://prove2.me/theorems/9d4a942e-157d-41e6-ab49-ea3d141f7c91
-- title:
--   Lemma 3.1 — SigComp is correct; refresh yields well-formed lists after $t_{ref}$ rounds; $X_j\sim_q X_k$ iff the commitment routine delivered from $P_k$ to $P_j$ in layer $q$
-- statement:
--   Let SigComp be the layered epoch signature scheme on parties $[n]$. Then SigComp is **correct** in the sense of Definition A.2: for every maximum depth $d$, label $g$, message $m$ and choice of lists, (1) signing with a well-formed $R_i$ returns a signature of depth $d$ that $P_i$ accepts at depth $d$; (2) if $1\le q\le d$, $X_j\sim_q X_k$ and $\mathrm{Verify}_j(i,m,\hat\sigma,R_j,q)=1$, then $\mathrm{Forward}_{j\to k}$ returns $\hat\sigma'\neq\bot$ with origin $i$, message $m$, holder $k$, depth $q-1$ and $\mathrm{Verify}_k(i,m,\hat\sigma',R_k,q-1)=1$; (3) acceptance implies holder $=j$ and $q=\mathrm{depth}(\hat\sigma)\le d$, and successful forwarding implies acceptance, $1\le q\le d$ and present, locally valid forwarding information; (4) in every execution of a model satisfying Section 3.1, a correct party that outputs refresh lists obtains well-formed lists.
--
--   Moreover, in every execution of a model satisfying Section 3.1 (common start $\tau_0$, durations $t_N$, $t_C$), every party that follows refresh obtains well-formed lists after
--   $$t_{ref}=t_N+d\,t_C$$
--   rounds, and for two parties $P_j$, $P_k$ that follow refresh and every $1\le q\le d$,
--   $$X_j\sim_q X_k \iff \text{the commitment routine delivered from } P_k \text{ to } P_j \text{ in layer } q.$$
--   The first part is the algebra of the local algorithms; the second says which directed pairs receive valid forwarding information, the clause that Definition A.4 asks a construction to state.
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
-- source:
--   Lenzen, Loss, Shi, Fresh Signatures without Fresh Keys, STOC 2027 submission (manuscript sha256 ac05cb97…), p. 14, Lemma 3.1

import Mathlib
import Definitions.Def_FreshSig_Layered_Term
import Definitions.Def_FreshSig_Layered_Execution
import Definitions.Def_FreshSig_Layered_EpochScheme
import Definitions.Def_FreshSig_Layered_SigComp

namespace FreshSig.Layered

/-- **Lemma 3.1 (Correctness).** SigComp on the party set `[n]` is correct in the sense of
Definition A.2: local correctness, forwardability and rejection for every maximum depth, message
and choice of lists, and refresh correctness in every execution of a model satisfying
Section 3.1. In such a model, every party that follows refresh (is correct through round
`τ₀ + tref`) obtains well-formed lists in round `τ₀ + tref`, `tref = tN + d tC`; and for two
parties `P_j`, `P_k` that follow refresh up to their outputs `(R_j, A_j)`, `(R_k, A_k)` and every
`1 ≤ q ≤ d`, `X_j ∼_q X_k` holds exactly if the commitment routine delivered from `P_k` to `P_j`
in layer `q`. -/
theorem lemma_3_1 (n : ℕ) :
    (sigComp n).CorrectA2 n ∧
    ∀ (d : ℕ) (g : Term) (τ₀ tN tC : ℕ) (tr : Execution), SigComp.Sec31 n d g τ₀ tN tC tr →
      (sigComp n).RefreshCorrectIn n d g τ₀ tr ∧
      (∀ i < n, CorrectThrough tr τ₀ i (τ₀ + SigComp.tref tN tC d) →
        ∃ (p : Pos) (R : List Term) (A : List FwdRecord), p.1 = τ₀ + SigComp.tref tN tC d ∧
          evAt tr p = some (Event.refreshOut i g R A) ∧ (sigComp n).wellFormedLists d R A) ∧
      (∀ j < n, ∀ k < n, ∀ (pj pk : Pos) (Rj Rk : List Term) (Aj Ak : List FwdRecord),
        CorrectAt tr τ₀ j pj → evAt tr pj = some (Event.refreshOut j g Rj Aj) →
        CorrectAt tr τ₀ k pk → evAt tr pk = some (Event.refreshOut k g Rk Ak) →
        ∀ q : ℕ, 1 ≤ q → q ≤ d →
          ((sigComp n).Compat Rj Aj q k Rk ↔ SigComp.Delivered tr τ₀ g q k j)) := by sorry

end FreshSig.Layered
