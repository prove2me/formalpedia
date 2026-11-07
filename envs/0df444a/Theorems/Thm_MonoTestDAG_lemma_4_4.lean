-- Prove2me | Theorems.Thm_MonoTestDAG_lemma_4_4
-- name    : MonoTestDAG.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:09:34.821536+00:00
-- url     : https://prove2.me/theorems/8cfb65f1-59c2-4595-bd79-1ab1e75d26c3
-- title:
--   Lemma 4.4 — completeness of the YES distribution
-- statement:
--   Let $U=(L,R;E)$ have an $(s,4\varepsilon)$-PMRS witness $M=(M_1,\dots,M_s)$, let $G:=P(U)$, and for every $i$ let $w_i$ certify that $M_i$ is positive. Every function in the support of the YES distribution $D^+$ of §4.3 is monotone on $G$.
--
--   Differences from the source:
--   - encoding: Unif([s]) → `[NeZero s]`, which follows from the witness's s ≥ 1; reason: Lean needs the instance to form the uniform law
--   - reading: distributions over functions → `PMF` on functions; reason: for a non-discrete D the average acceptance probability needs joint measurability the paper never states; every distribution the paper constructs is finitely supported
--   - reading: s ∈ ℕ in Definition 4.3 → s ≥ 1, inside `IsPMRSWitness`; reason: [K] is defined only for positive K (p.1); the index i ∈ [s] and Unif([s]) need s ≥ 1
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Lemma 4.4, p.19

import Mathlib
import Definitions.Def_MonoTestDAG_dmon
import Definitions.Def_MonoTestDAG_IsPMRSWitness
import Definitions.Def_MonoTestDAG_yesDist

namespace MonoTestDAG

/-- **Lemma 4.4 (Completeness).** Let `U = (L, R; E)` be an `(s, 4ε)`-PMRS graph with an
`(s, 4ε)`-PMRS witness `M = (M_1, …, M_s)`, let `G := P(U)`, and for every `i` let `w_i` certify
that `M_i` is positive. Every function in the support of the YES distribution `D⁺` of §4.3 is
monotone on `G`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Lemma 4.4, p.19 (construction §4.3.1–4.3.2, pp.17–19).

**Formalization Note.** `[NeZero s]` makes `Unif([s])` a distribution; it follows from `s ≥ 1`,
which is part of the witness predicate. -/
theorem lemma_4_4 {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (EU : Finset (L × R)) (ε : ℝ) (s : ℕ) [NeZero s] (M : Fin s → Finset (L × R))
    (hM : IsPMRSWitness EU (4 * ε) s M) (w : Fin s → L ⊕ R → ℝ)
    (hw : ∀ i, IsPosWeight EU (M i) (w i)) :
    ∀ F ∈ (yesDist M w).support, IsMonotone (bipDAG EU) F := by sorry

end MonoTestDAG
