-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_Supplement_lemma_4_3
-- name    : LocalProbeMIS871.Greedy.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:04:39.890012+00:00
-- url     : https://prove2.me/theorems/acec37a2-b287-4820-bb93-260f29e5c389
-- title:
--   Lemma 4.3 — Uniform adaptive transcript total-variation bound
-- statement:
--   There exist an absolute $C>0$, an integer threshold $\Delta_0\ge2$, and positive constants $K_\Delta$ depending only on $\Delta$, such that for every $\Delta\ge\Delta_0$, every integer $q\ge1$, every admissible $m$ and every deterministic adaptive procedure $B$ using at most $q$ individual oracle calls,
--
--   $$d_{\rm TV}(T_0,T_1)\le \frac{Cq}{\Delta^{3/2}}+\min\left\{1,\frac{K_\Delta(q+1)^2}{m}\right\}.$$
--
--   Here $T_i$ is the observed transcript of that same procedure on the actual finite $D_i$ experiment, comprising the uniform hidden-$A$ query's label, all probes and replies, and any final output. The procedure may use $n,\Delta,k,\ell,m$ as free advice and has no MIS-correctness obligation. The constants are uniform over $q,m,B$ and its output type; $C$ is also uniform over $\Delta$. The statement includes $n\le2q+1$ and post-simplification graphs whose degrees have dropped.
--
--   This is the indistinguishability estimate used in the companion lower bound. The probability distance concerns finite inputs, rather than the auxiliary unbounded explorations of the proof.
--
--   **Formalization Note** A deterministic procedure is an arbitrary next-action rule on root and history; all bounded procedures have a representation whose next action after $q$ calls stops or diverges. A transcript is the absorbing state after $q+1$ local actions, paired with the initial root. The output type is arbitrary, and real exponentiation represents $\Delta^{3/2}$.
--
--   Differences from the source:
--   - encoding: vertices labeled in [n] → vertices represented by Fin n; reason: adding one to each label is a bijection and preserves all graph and oracle information
--   - encoding: the finite distributions D₀ and D₁ of §4.1 → uniform counting on finite permutation seeds followed by the specified graph, list and query maps; reason: all fibers have constant multiplicity, so these are exactly the source laws, with no conditioning
--   - encoding: a procedure using at most q probes and its transcript → a history policy normalized to request no probe at histories of length at least q, observed through step q+1; reason: all source q-probe interactions have this representation, including early stopping or local divergence; unreachable histories can be completed arbitrarily
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 27, PDF p. 29, Lemma 4.3

import Definitions.Def_LocalProbeMIS871_Greedy_Supplement_Observation

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
universe uLemma43

namespace LocalProbeMIS871.Greedy.Supplement

/-- Lemma 4.3, printed p.27 / PDF29; no restriction n > 2q+1 and no MIS premise. -/
theorem lemma_4_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ Δ₀ : ℕ, 2 ≤ Δ₀ ∧ ∃ K : ℕ → ℝ,
      ∀ Δ : ℕ, Δ₀ ≤ Δ → 0 < K Δ ∧
        ∀ q : ℕ, 1 ≤ q → ∀ m : ℕ, Admissible Δ m →
          ∀ (O : Type uLemma43) (B : Procedure (graphSize Δ m) O), BoundedProcedure B q →
            transcriptTV B q ≤ C * (q : ℝ) / (Δ : ℝ) ^ (3 / 2 : ℝ) + rho K Δ q m := by sorry

end LocalProbeMIS871.Greedy.Supplement
