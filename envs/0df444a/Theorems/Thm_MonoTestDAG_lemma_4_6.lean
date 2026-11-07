-- Prove2me | Theorems.Thm_MonoTestDAG_lemma_4_6
-- name    : MonoTestDAG.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:21.895004+00:00
-- url     : https://prove2.me/theorems/59d0e639-7a24-4171-9fe9-b5786ac39c8a
-- title:
--   Lemma 4.6 — identical transcripts when no edge of $M_i$ has both endpoints queried
-- statement:
--   In the setting of §4.3, fix $i\in[s]$ and a query set $Q\subseteq L\cup R$. If $Q$ does not contain both endpoints of any edge of $M_i$, then the joint distribution of the answers on $Q$ is identical under $D^+_i$ and $D^-_i$:
--   $$
--   \mathrm{Tr}(D^+_i,Q)=\mathrm{Tr}(D^-_i,Q).
--   $$
--   This is the indistinguishability behind every lower bound of the paper.
--
--   Differences from the source:
--   - encoding: "chosen non-adaptively" → a fixed set Q; reason: a non-adaptive query set is fixed once the seed is fixed
--   - reading: s ∈ ℕ in Definition 4.3 → s ≥ 1, inside `IsPMRSWitness`; reason: [K] is defined only for positive K (p.1); the index i ∈ [s] and Unif([s]) need s ≥ 1
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Lemma 4.6, p.20

import Mathlib
import Definitions.Def_MonoTestDAG_IsPMRSWitness
import Definitions.Def_MonoTestDAG_yesDist
import Definitions.Def_MonoTestDAG_transcript

namespace MonoTestDAG

/-- **Lemma 4.6 (Identical transcripts when no edge of `M_i` has both endpoints queried).** In the
setting of §4.3, fix `i ∈ [s]` and a query set `Q ⊆ L ∪ R` chosen non-adaptively. If `Q` does not
contain both endpoints of any edge in `M_i`, then the joint distribution of the answers on `Q` is
identical under `D⁺_i` and `D⁻_i`: `Tr(D⁺_i, Q) = Tr(D⁻_i, Q)`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Lemma 4.6, p.20. -/
theorem lemma_4_6 {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (EU : Finset (L × R)) (ε : ℝ) (s : ℕ) (M : Fin s → Finset (L × R))
    (hM : IsPMRSWitness EU (4 * ε) s M) (w : Fin s → L ⊕ R → ℝ)
    (hw : ∀ i, IsPosWeight EU (M i) (w i)) (i : Fin s) (Q : Finset (L ⊕ R))
    (hQ : ∀ e ∈ M i, ¬ ((Sum.inl e.1 : L ⊕ R) ∈ Q ∧ (Sum.inr e.2 : L ⊕ R) ∈ Q)) :
    transcript (condYes (M i) (w i)) Q = transcript (condNo (M i) (w i)) Q := by sorry

end MonoTestDAG
