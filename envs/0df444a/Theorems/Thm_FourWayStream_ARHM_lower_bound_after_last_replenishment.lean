-- Prove2me | Theorems.Thm_FourWayStream_ARHM_lower_bound_after_last_replenishment
-- name    : FourWayStream.ARHM.lower_bound_after_last_replenishment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:51.259147+00:00
-- url     : https://prove2.me/theorems/7585f00b-d522-4fbe-a80c-47b3c0eacc05
-- title:
--   Proposition 5.13 — lower bound after the last replenishment: $q\ge ps-1-s(s^2-1)/(6(N-1))$
-- statement:
--   **Proposition 5.13 (Lower bound after the last replenishment).** Let $N\ge2$ be even, $s\ge1$, and $X$ uniform, with the algorithm and the one-factorization $F$ fixed independently of $X$. Consider an admissible cut (Definition 5.8) whose suffix consists of $s$ requests and no updates. The requests ask for independent uniform factors and are revealed and answered one at a time. If an algorithm with $q$ qubits of live memory answers all $s$ requests correctly with probability at least $p$ in this experiment, then
--   $$q\ge ps-1-\frac{s(s^2-1)}{6(N-1)}.$$
--   If $s\le\sqrt N$ and $p\ge2/3$, then $q\ge s/2-1$ and thus $q=\Omega(s)$.
--
--   Once no further updates arrive, the memory must carry linearly many qubits in the number of remaining requests.
--
--   Differences from the source:
--   - reading: §4.2: a classical controller applies, for every item, a circuit from a fixed finite set of gates and measurement operators to an array of qubits → every item is processed by an arbitrary quantum instrument (finite complete Kraus family indexed by the output) on the memory C^d; the finite gate set is not modelled; reason: §4.2 is ambiguous: it states that the lower bounds hold for arbitrary channels, and the paper's own algorithm (Prop 5.7) uses exact phases e^{iπ/µ} and exact Fourier and matching-basis measurements, which are not circuits over a fixed finite gate set
--   - generalization: algorithms of the §4.2 model, in which the stage enters only through memory → also algorithms whose instruments depend on the stage, provided the cut position is determined by the public randomness (for stage-independent algorithms the cut is as general as Definition 5.8); reason: a larger class; the paper's algorithms are the stage-independent ones
--   - reading: an admissible cut whose suffix consists of s requests → the tags of the suffix requests are determined by the public randomness; reason: as in Lemma 5.9: Bob must know the request items; true of the cuts the paper uses
--   - generalization: the prefix of an ARHM stream → an arbitrary list of items determined by (r, private randomness, x); reason: a larger set of prefixes; the ARHM prefixes are a special case
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §5.3, p.24, Proposition 5.13

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Information
import Definitions.Def_FourWayStream_ARHM_Protocols

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Proposition 5.13 (Lower bound after the last replenishment), p.24. Let `N ≥ 2` be even,
`s ≥ 1`, `X` uniform, the algorithm and the one-factorization fixed independently of `X`. Consider an
admissible cut whose suffix consists of `s` requests and no updates, the requests asking for
independent uniform factors, revealed and answered one at a time. If an algorithm with `q` qubits of
live memory answers all `s` requests correctly with probability at least `p` in this experiment, then
`q ≥ ps − 1 − s(s² − 1)/(6(N − 1))`; if `s ≤ √N` and `p ≥ 2/3`, then `q ≥ s/2 − 1`. The cut position
may depend on `X` and private randomness for stage-independent algorithms (the paper's model) and
must be public for stage-dependent ones. -/
theorem lower_bound_after_last_replenishment (N m L s : ℕ) (hN : Even N) (hN2 : 2 ≤ N)
    (hs : 1 ≤ s) (F : Fin (N - 1) → Finset (Sym2 (Fin N))) (hF : IsOneFactorization F)
    (A : QStreamAlg N m L) (hA : A.Valid) (C : Cut N m L s) (hC : C.Valid)
    (hpos : A.StageIndependent ∨ C.PositionPublic) (q : ℕ) (hq : A.space ≤ q) (p : ℝ)
    (hp : p ≤ C.qCutSucc A F) :
    p * s - 1 - s * ((s : ℝ) ^ 2 - 1) / (6 * ((N : ℝ) - 1)) ≤ q ∧
    ((s : ℝ) ≤ Real.sqrt N → 2 / 3 ≤ p → (s : ℝ) / 2 - 1 ≤ q) := by sorry

end FourWayStream.ARHM
