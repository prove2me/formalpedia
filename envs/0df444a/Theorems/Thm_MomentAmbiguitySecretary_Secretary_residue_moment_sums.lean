-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_residue_moment_sums
-- name    : MomentAmbiguitySecretary.Secretary.residue_moment_sums
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:09.557197+00:00
-- url     : https://prove2.me/theorems/60b8a219-bdd3-4d22-9229-1c09e493ab2b
-- title:
--   Lemma 8.8 — equal residue sums and common normalization
-- statement:
--   Fix integers $B,N\ge2$. For every moment order $t\ge0$ and residue $0\le h<N$, the defining residue series converges and
--
--   $$W_h(t)=\sum_{j\equiv h\pmod N}w_jB^{tj}=\frac{G_N(B^t)}{N}.$$
--
--   In particular all $W_h(0)$ equal the concrete common normalizer $W=W_0(0)$, and $1\le W<4$.
--
--   The convergence and common positive normalization make the atomic families meaningful.
--
--   Differences from the source:
--   - encoding: real residue sums equal a generating-function value → HasSum and the same identity embedded in the complex numbers; reason: embedding a real residue sum in the complex numbers preserves the identity and asserts that the generating-function value is real
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied preprint, Lemma 8.8, PDF/printed p.31, SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Separator

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary

/-- Lemma 8.8, pinned preprint PDF/printed pp.31–32. -/
theorem residue_moment_sums (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    (∀ (t : ℕ) (h : Fin N),
      HasSum (residueTerm B N h.val t) (residueSum B N h.val t) ∧
      (residueSum B N h.val t : ℂ) = entireProduct B N ((B : ℂ) ^ t) / (N : ℂ)) ∧
    (∀ h : Fin N, residueSum B N h.val 0 = normalizer B N) ∧
    1 ≤ normalizer B N ∧ normalizer B N < 4 := by sorry

end MomentAmbiguitySecretary.Secretary
