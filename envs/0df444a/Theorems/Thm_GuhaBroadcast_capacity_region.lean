-- Prove2me | Theorems.Thm_GuhaBroadcast_capacity_region
-- name    : GuhaBroadcast.capacity_region
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:37.25848+00:00
-- url     : https://prove2.me/theorems/070e4443-6f44-4eb3-b898-7b856d190d9b
-- title:
--   Capacity region of the bosonic broadcast channel for $\eta>1/2$, with no conjecture assumed
-- statement:
--   Let $\tfrac12<\eta\le1$ be the transmissivity of the beam splitter (6)–(7) to Bob, with vacuum environment, and $\bar N\ge0$ the mean input photon-number budget. A rate pair $(R_B,R_C)$ is achievable if there are codes with Bob decoding $(m,k)$ and Charlie decoding $k$, block lengths $n\to\infty$, message sets of sizes about $e^{nR_B}$, $e^{nR_C}$, codebook-averaged photon number at most $\bar N$ per use, and error $\epsilon_n\to0$ for every message pair. The capacity region is the convex hull of the closure of the achievable pairs (p.2). Then the capacity region is
--
--   $$
--   \Big\{(R_B,R_C)\ge0:\ \exists\,\beta\in[0,1],\ R_B\le g(\eta\beta\bar N),\ R_C\le g\big((1-\eta)\bar N\big)-g\big((1-\eta)\beta\bar N\big)\Big\},
--   $$
--
--   where $g(x)=(1+x)\log(1+x)-x\log x$, and the capacity region of codes whose codewords are products of coherent states (with arbitrary collective decoding) is the same set.
--
--   The paper proves this assuming a minimum-output-entropy conjecture (Strong conjecture 2). The conjecture is used once, at (18), on states of finite energy, where the entropy photon-number inequality (Proved on the platform as `OAI.EntropyPhotonNumber.entropy_photon_number_inequality`) gives it, so the statement here carries no conjecture hypothesis; the printed conditional theorem is the platform's Open `QAlgorithms.Papers.Independent.Next46.P32.conditional_broadcast_capacity` and follows from this one.
--
--   **Formalization Note** All objects are the published ones of `QAlgorithms.Papers.Independent.Next46.P32`: `sourceRegion` (convex hull of the closure of achievable pairs; the optional flag `true` restricts to product coherent codewords), `broadcast`, `thermalRegion`. Rates and entropies are in nats.
--
--   Differences from the source:
--   - generalization: 'Assuming this conjecture to be true' (Strong conjecture 2, p.5) → no conjecture hypothesis; reason: the converse uses the conjecture only at (18), on finite-energy codewords, where the Proved entropy photon-number inequality (e96b6eda) supplies it; the printed conditional statement (Open, 496bde42) follows by ignoring the hypothesis
--   - reading: no range of η in (8)-(9); 'if η > 1/2' in the proof, 0 ≤ η ≤ 1 at (6)-(7) → 1/2 < η ≤ 1; reason: the result is stated for the degraded channel, which the proof requires η > 1/2 for
--   - reading: 'This rate region is additive' → carried by the equality of the capacity region with the single-letter region (8)-(9); reason: the paper gives no separate claim; 'additive' means no regularization over n is needed, unlike (4)-(5)
--   - reading: 'achievable with single channel use coherent-state encoding with the distributions (10)-(11)' → the capacity region of codes with product coherent-state codewords (collective decoding) equals the region; the distributions are carried by the referenced inner bound; reason: codewords are products of single-use coherent states; decoding stays collective ('joint detection over long codewords', p.4)
--   - encoding: a rate pair is achievable if there are (2^{nR_B}, 2^{nR_C}, n, ε_n) codes with ε_n → 0, with message sets of size 2^{nR}, logarithm base unspecified → R_B, R_C ≥ 0 and, for every ε, δ > 0, codes at every large n with error ≤ ε and log M_B / n ≥ R_B − δ, log M_C / n ≥ R_C − δ, M the message-set cardinality, natural logarithm (the same nonnegativity R ≥ 0 is part of the region (8)-(9)); reason: 2^{nR} need not be an integer, so rates are approached within δ; message-set sizes 2^{nR} ≥ 1 make rates nonnegative; a change of base scales both regions
--   - encoding: mean input photon-number constraint ⟨â†â⟩ ≤ N̄, 'averaged over the entire codebook' (p.3) → codebook-average total block energy ≤ nN̄; reason: the paper's own reading of the constraint on p.3
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, eqs. (8)-(11), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, Eqs. (8)–(11), p.2 (PDF page; the paper prints no page numbers): "the ultimate
capacity region of the single-mode noiseless Bosonic broadcast channel (see Fig. 2) with a mean input
photon-number constraint ⟨â†â⟩ ≤ N̄ is R_B ≤ g(ηβN̄), and (8) R_C ≤ g((1 − η)N̄) − g((1 − η)βN̄), (9) for
0 ≤ β ≤ 1, where g(x) = (1 + x) log(1 + x) − x log(x). This rate region is additive and achievable with
single channel use coherent-state encoding".

For `1/2 < η ≤ 1` and `N̄ ≥ 0`: the classical capacity region (convex hull of the closure of all
achievable rate pairs, p.2), over all codes, equals the region (8)–(9), and so does the capacity region
of codes whose codewords are products of coherent states.

**Formalization Note.** **The paper's hypothesis "Assuming this conjecture to be true" (Strong
conjecture 2, p.5) is removed**: the converse uses the conjecture only at (18), on finite-energy states,
where the Proved entropy photon-number inequality supplies it (see `eq_18`). The printed conditional
statement is the Open platform theorem
`QAlgorithms.Papers.Independent.Next46.P32.conditional_broadcast_capacity` and follows from this one.
Reading R1: `1/2 < η ≤ 1` (the proof's "if η > 1/2" and (6)–(7)). Reading R2: "additive" is carried by
equality with the single-letter region. Reading R3: "coherent-state encoding" is `coherentOnly := true`
(product coherent codewords, collective decoding). Rates are in nats from message-set cardinalities, the
budget is the codebook-average block energy `≤ n N̄`, error is required for every message pair; all
objects are the published ones of `QAlgorithms.Papers.Independent.Next46.P32`. -/
theorem capacity_region (eta Nbar : ℝ) (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (hNbar : 0 ≤ Nbar) :
    sourceRegion (fun n => broadcast n eta) Nbar = thermalRegion eta (1 - eta) Nbar ∧
      sourceRegion (fun n => broadcast n eta) Nbar true = thermalRegion eta (1 - eta) Nbar := by sorry

end GuhaBroadcast
