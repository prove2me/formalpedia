-- Prove2me | Theorems.Thm_IncrementalER_Supplement_theorem_6_1
-- name    : IncrementalER.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:55:21.045252+00:00
-- url     : https://prove2.me/theorems/2bbc7766-3a8f-4ead-b765-7ae24ec2e058
-- title:
--   Theorem 6.1 — dynamic low-recourse vertex sparsifier
-- statement:
--   Let $G_0$ have active vertex set $V_0$, $m_0$ initial edge occurrences, $n_0=|V_0|$, capacity ratio $U$, and protected set $S$. Let $0<\varepsilon<1/2$ and $1<k<m_0$. Under batches of legal vertex insertions and deletions, edge insertions and deletions, and protected-terminal insertions, assume no protected vertex is deleted and
--   $$
--   R_{\mathrm{eff}}^G(u,v)\le2R_{\mathrm{eff}}^{G_0}(u,v)
--   $$
--   for every distinct surviving $u,v\in V_0$ throughout the sequence.
--
--   One uniform randomized exact-real-RAM program maintains $S\subseteq T\subseteq V$ and a positive-capacity multigraph $H$ supported on $T$ such that $|T|=\widetilde O(m_0/k)$,
--   $$(1-\varepsilon)\operatorname{SC}(G,T)\preceq H\preceq(1+\varepsilon)\operatorname{SC}(G,T),$$
--   $\mathbb E|E(H)|=\widetilde O(\varepsilon^{-2}m_0/k)$, and $U_H=\widetilde O(U\varepsilon^{-4}m_0^3n_0^2)$. Against an oblivious sequence of at most $m_0/(2k)$ elementary updates, correctness is high probability, expected total output recourse is $\widetilde O(\varepsilon^{-2}m_0/k)$, and expected total work including initialization is $\widetilde O(m_0(k^{c_{\rm out}}+k^4\varepsilon^{-4}))$ for an absolute $c_{\rm out}>1$.
--
--   Differences from the source:
--   - encoding: changing finite vertex set and multigraph → an active subset of one finite ambient pool and stable natural identifiers for edge occurrences; reason: every source update sequence embeds in a sufficiently large pool, and identifiers preserve parallel-edge multiplicity and exact deletion
--   - encoding: graph H supported on T and Loewner approximation to SC(G,T) → a decoded positive-capacity edge list supported on T and PSD differences against the Schur complement over the active set; reason: this is the same multigraph and matrix order, while excluding inactive ambient vertices from elimination
--   - encoding: expected size, recourse, and work → lower integrals of nonnegative edge counts, multiset edge/vertex changes, and charged instructions; reason: prevents non-integrable expectations from receiving Lean's junk value zero
--   - generalization: graph edges join distinct vertices → initial and inserted edge lists may also contain loops, ignored by all graph quantities; reason: removing loops preserves every source graph and update while only decreasing edge-count upper bounds
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 6.1, p.37

import Mathlib
import Definitions.Def_IncrementalER_Supplement_theorem61Spec

set_option autoImplicit false

namespace IncrementalER.Supplement

/-- **Theorem 6.1** (Goranci et al., STOC 2027 submission, manuscript sha256 a0415fd5…, p.37).
One uniform online exact-real-RAM program maintains the terminal set and approximate Schur
complement through the full batch-update interface, with every printed output, capacity-ratio,
effective-resistance, adversary, update-budget, expected recourse and expected work clause. -/
theorem theorem_6_1 :
    ∀ A : ℝ, 0 < A → ∀ q : ℕ, ∀ c : ℝ, 1 < c →
      ∃ P : PNormReg.Program, ∃ C : ℝ, ∃ r : ℕ, ∃ cOut : ℝ,
        A ≤ C ∧ q ≤ r ∧ theorem61Spec P C r c cOut := by sorry

end IncrementalER.Supplement
