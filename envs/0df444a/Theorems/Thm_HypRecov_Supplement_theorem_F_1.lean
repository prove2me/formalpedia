-- Prove2me | Theorems.Thm_HypRecov_Supplement_theorem_F_1
-- name    : HypRecov.Supplement.theorem_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:31:50.109404+00:00
-- url     : https://prove2.me/theorems/cfc0d558-37b4-4e6c-9ae5-d7cb44cbf6ec
-- title:
--   Theorem F.1 — simultaneous low-link availability on every small cut
-- statement:
--   Let $K\ge1$, let $M$ be a power of two with $2\le M\le2K$, let $0<\eta<1$, and set
--   $$q=\min\{r,2+\log_2M\}.$$
--   There is one uniform randomized one-pass linear sketch using $\widetilde O(nrK)$ bits and polynomial time that returns complete link records for a family of pairs. With probability at least $1-\eta$, simultaneously for every $S\subseteq V$ with $|\delta_H(S)|\le K$, every two-section pair $uv$ crossing $S$ with $1\le w_{uv}<M$ has a returned record.
--
--   Every returned record has exact codegree $1\le w_f<M$ and the complete tag list of $L_f$. All represented tags are nonzero and globally distinct. On every non-aborted execution, the total number of stored tag occurrences is $\widetilde O(nrK)$. Seeds, finite precision, output and decoding workspace are included.
--
--   Differences from the source:
--   - reading: Theorem F.1 uses the failure parameter $\eta$ without stating its range → `0 < eta` and `eta < 1`; reason: this is the unique meaningful range for the displayed success probability and logarithmic failure-dependent resources
--   - encoding: unordered pairs and short field tags → two-element `Finset`s and injective nonzero natural-number codes for tags; reason: the codes preserve pair/link equality, nonzeroness and global distinctness while exposing their complete binary storage cost
--   - encoding: randomized one-pass linear sketch with $\widetilde O(nrK)$ space, polynomial time and an off-good-event cap → uniform TM2 machines and a terminal-state function with explicit coin, additive/subtraction, all-stack and parsed-output bounds; reason: this retains the simultaneous per-stream probability and the deterministic cap on every non-aborted output
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem F.1, pp.41-43 (PDF pp.42-44)

import Mathlib
import Definitions.Def_HypRecov_Supplement_LinkRecord

set_option autoImplicit false

namespace HypRecov.Supplement

/-- **Theorem F.1 (Low-link availability on all small cuts).** Zhang, Chen, Shen, *Hypergraph
Recovery from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…),
Theorem F.1, pp.41–43 (PDF pp.42–44).

For `K ≥ 1` and a power of two `M` with `2 ≤ M ≤ 2K`, one uniform randomized one-pass linear
sketch at order `min{r,2+log₂ M}` returns complete, correctly labelled records covering every
positive pair of codegree below `M` that crosses any cut of value at most `K`, simultaneously with
failure at most `eta`.  Every returned record is genuinely low, tags are nonzero and globally
distinct on represented original edges, and every non-aborted decoder output obeys the
`O-tilde(nrK)` stored-tag cap.  Seeds, precision and decoder workspace are included.

**Formalization Note.** An unordered pair is a two-element `Finset`.  Short field tags are represented
by nonzero natural-number codes; the output encoding and all-stack budget charge their complete bit
representations. -/
theorem theorem_F_1 :
    ∃ (A : HypRecov.LinearSketch) (C c : ℕ),
      ∀ (n r K M : ℕ) (eta : ℝ), 2 ≤ r → r ≤ n → 1 ≤ K →
        2 ≤ M → M ≤ 2 * K → (∃ t : ℕ, M = 2 ^ t) → 0 < eta → eta < 1 →
        LowLinkSketchGuarantee A C c n r K M (min r (2 + Nat.log 2 M)) eta
    := by sorry

end HypRecov.Supplement
