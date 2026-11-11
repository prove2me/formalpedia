-- Prove2me | Theorems.Thm_FreshSig_Layered_lemma_3_2
-- name    : FreshSig.Layered.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:44:14.256998+00:00
-- url     : https://prove2.me/theorems/ce19cb0b-deb0-4168-92e4-7d14e184cbbf
-- title:
--   Lemma 3.2 — no reference value from before the start: the top path value $\rho_0$ of a signature accepted by a party following refresh does not occur before $\tau_0$
-- statement:
--   In every execution of a model satisfying Section 3.1 with common start round $\tau_0$, let $P_j$ follow refresh and let $(R_j,A_j)$ be the lists of this refresh. If $P_j$'s verification accepts a signature $\hat\sigma=(i,m,\sigma,U,W,G)$ against $R_j$, at any depth $q$, then the first path value $\rho_0$ of $W$ does not occur before $\tau_0$:
--   $$\rho_0\notin\mathrm{Sub}\big(K(h_0)\big),$$
--   where $h_0$ is the execution prefix immediately before round $\tau_0$. This is the freshness step of the unforgeability proof: a signature prepared before the start would have fixed $\rho_0$ before the start.
--
--   Differences from the source:
--   - generalization: a model M+ satisfying Section 3.1: synchronous rounds with common start τ0, authentic possibly lossy channels, the corruption and exposure rules of A.3 with a preparation phase A0, and nonce and commitment routines satisfying Definitions A.5 and A.9 against every admissible adversary with precorruptions, durations tN and tC → every execution `tr` (rounds of finite event lists) with `SigComp.Sec31 n d g τ₀ tN tC tr`: the symbolic rules hold (`Admissible`), every party runs SigComp's refresh and verification while it is correct (`FollowsRefresh`, `FollowsVerification`), and the routines meet the guarantees of A.5 (freshness at every correct party, §2.4) and A.9 in that execution; no requirement on channels, any number of adaptive corruptions, and every signing interface callable by anyone at any time, before and after τ0; reason: every execution of such an M+ satisfies these conditions (its routines meet their guarantees against its adversary, and everything anyone handles is in the record and obeys the public rules), and the extra adversarial freedom only enlarges the class; the scheme's guarantees are local and use none of the restrictions dropped
--   - generalization: a public epoch label g → any term `g : Term`; reason: no clause uses publicity of g; a public label is one instance (for a label no correct party can compute, no correct party completes refresh, and the clauses about correct parties hold trivially)
--   - generalization: the term set T of Appendix A.1 (constants, atoms, tuples, signatures, roots, leaves, proofs) → `Term` with, in addition, `pid i` (party identities as public constants) and `ext k i x`, outputs of other protected interfaces such as the counter-bound signer of Example A.7, created only by `extCall` events; reason: covers nonce routines built on the counter-bound signer, which §3.1 names; with no `extCall` event the extra constructor never occurs
--   - encoding: parties P1, …, Pn and coordinates 1, …, n → indices 0, …, n − 1 (`i < n`), coordinate j of a vector belonging to party j; reason: index shift
--   - encoding: ⊥ entries, proofs and outputs; Verify ∈ {0, 1} → `Option` (`none` = ⊥); verification as a proposition `verify …` (holds iff the output is 1); reason: Lean convention; same instances
--   - reading: every root and proof is tagged with its type and, where needed, its invocation (p. 62) → `root ℓ V` and `prf ℓ V j` carry the depth ℓ and the vector, not an invocation tag (the explicit-vector realisation of Example A.10); reason: SigComp never needs invocation tags; the depth typing and the containment of entries are kept
--   - encoding: σ̂ = (i, m, σ, U, W, G) → the tuple term `tup [pid i, m, σ, tup (U.map pid), tup W, tup G]`, parsed by `SigComp.parse`; reason: an epoch signature is a term (it contains its ideal signature as a structural subterm)
--   - encoding: an execution, its prefixes, the record K(h), occurrence before τ, events grouped into rounds → `Execution = ℕ → List Event`; positions `(round, index)` in lexicographic order; `record tr p` = all terms of the events strictly before p; occurs before round τ0 = `∈ Sub (record tr (τ₀, 0))`; reason: direct transcription; the record is cumulative by construction
--   - reading: Refresh: nonce routine, then layers ℓ = 1..d; refresh takes tref = tN + d·tC rounds → lockstep schedule: nonce routine invoked in round τ0, layer ℓ in round τ0 + tN + (ℓ − 1)·tC once the outputs it needs are available, output in round τ0 + tN + d·tC once all are available; "takes tref rounds" = every party correct through round τ0 + tref outputs in round τ0 + tref; reason: synchronous parties start the joint routines together and each routine is given its stated duration
--   - reading: a party that follows the protocol / follows refresh; a correct verifier → corruption is an event `corrupt i`; `CorrectAt tr τ₀ i p`: no execution-phase corruption of i up to p (preparation-phase corruption does not count); following refresh = correct up to the refresh output, or through round τ0 + tref where completion is claimed; reason: A.3: a party is correct up to an event if it followed the protocol throughout that prefix; uncorrupted parties run the protocol
--   - reading: an invoking party obtains a local output (Definitions A.5, A.9) → one output event per invocation at a correct party (`single_output`); reason: the routines' output is a single value per invocation
--   - reading: "If Pj accepts σ̂ … against the list Rj of this refresh, at any depth" → `SigComp.verify n d g j i m σ̂ Rj q` for the list Rj of P_j's refresh output, for any q (no acceptance event is required); reason: the lemma is about the outcome of verification against R_j
-- source:
--   Lenzen, Loss, Shi, Fresh Signatures without Fresh Keys, STOC 2027 submission (manuscript sha256 ac05cb97…), p. 14, Lemma 3.2

import Mathlib
import Definitions.Def_FreshSig_Layered_Term
import Definitions.Def_FreshSig_Layered_Execution
import Definitions.Def_FreshSig_Layered_EpochScheme
import Definitions.Def_FreshSig_Layered_SigComp

namespace FreshSig.Layered

/-- **Lemma 3.2 (No reference value from before the start).** In every execution of a model
satisfying Section 3.1, let `P_j` follow refresh up to its refresh output `(R_j, A_j)`. If
`P_j`'s verification accepts `σ̂ = (i, m, σ, U, W, G)` against `R_j`, at any depth `q`, then the
first path value `ρ₀` does not occur before the common start `τ₀`, i.e.
`ρ₀ ∉ Sub(K(h₀))` for the prefix `h₀` before round `τ₀`. -/
theorem lemma_3_2 (n d : ℕ) (g : Term) (τ₀ tN tC : ℕ) (tr : Execution)
    (hM : SigComp.Sec31 n d g τ₀ tN tC tr)
    (j : ℕ) (hj : j < n) (pR : Pos) (Rj : List Term) (Aj : List FwdRecord)
    (hcorr : CorrectAt tr τ₀ j pR) (hout : evAt tr pR = some (Event.refreshOut j g Rj Aj))
    (i : ℕ) (m σhat : Term) (q : ℕ) (hacc : SigComp.verify n d g j i m σhat Rj q)
    (σ : Term) (U : List ℕ) (W G : List Term)
    (hparse : SigComp.parse σhat = some (i, m, σ, U, W, G))
    (ρ₀ : Term) (hρ₀ : W[0]? = some ρ₀) :
    ¬ OccursBefore tr (τ₀, 0) ρ₀ := by sorry

end FreshSig.Layered
