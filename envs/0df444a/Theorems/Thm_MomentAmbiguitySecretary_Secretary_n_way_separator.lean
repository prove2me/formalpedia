-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_n_way_separator
-- name    : MomentAmbiguitySecretary.Secretary.n_way_separator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:15.636866+00:00
-- url     : https://prove2.me/theorems/886a4eca-6a0f-428f-83a3-afdd0aa5461b
-- title:
--   Theorem 3.2 — full N-way residue separator
-- statement:
--   Fix integers $B,N\ge2$. The concrete coefficients $w_j$ are the unique coefficients of the everywhere-convergent generating series $G_N(z)=\sum_{j\ge0}w_jz^j$. The common normalizer $W=W_0(0)$ satisfies $1\le W<4$, and for each $0\le h<N$,
--
--   $$\mu_h(\{B^j\})=\begin{cases}w_j/W&j\equiv h\pmod N,\\0&\text{otherwise}\end{cases}$$
--
--   defines a probability measure of full mass on $\{B^j:j\equiv h\pmod N\}$. These residue sets are pairwise disjoint. All powers are integrable and every pair of measures has equal moments. In addition, for every $j\ge0$,
--
--   $$B^{-e(j)}\le w_j\le2^jB^{-e(j)},\qquad j-e(j)\le N-1,$$
--
--   with equality in the last inequality exactly for $N-1\le j\le2N-2$; here $e(j)$ is the quotient-remainder exponent defined in the construction.
--
--   This states every clause of the separator, rather than only existence of moment-equivalent laws.
--
--   Differences from the source:
--   - encoding: the generating coefficients and a common normalizer defining probability laws → Taylor-defined coefficients and the concrete normalizer W_0(0), with atomic measures on nonnegative reals; reason: the source proof identifies this normalizer and these coefficients uniquely; the construction retains all original instances
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied preprint, Theorem 3.2, PDF/printed p.8, SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Separator

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary

/-- Theorem 3.2, pinned preprint PDF/printed p.8, proved pp.29–34.
All laws are the concrete countable atomic measures, not arbitrary witnesses. -/
theorem n_way_separator (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    (∀ z : ℂ, HasSum (fun j : ℕ => (coefficient B N j : ℂ) * z ^ j)
      (entireProduct B N z)) ∧
    (∀ a : ℕ → ℂ,
      (∀ z : ℂ, HasSum (fun j : ℕ => a j * z ^ j) (entireProduct B N z)) →
      a = fun j => (coefficient B N j : ℂ)) ∧
    1 ≤ normalizer B N ∧ normalizer B N < 4 ∧
    (∀ h : Fin N, IsProbabilityMeasure (residueMeasure B N h.val) ∧
      residueMeasure B N h.val (residueSupport B N h.val) = 1 ∧
      (∀ j : ℕ, residueMeasure B N h.val {((B : ℝ≥0) ^ j)} =
        ENNReal.ofReal (if j % N = h.val then coefficient B N j / normalizer B N else 0)) ∧
      (∀ t : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ t)
        (residueMeasure B N h.val))) ∧
    (∀ h h' : Fin N, h ≠ h' → Disjoint (residueSupport B N h.val)
      (residueSupport B N h'.val)) ∧
    (∀ (h h' : Fin N) (t : ℕ),
      (∫ x : ℝ≥0, (x : ℝ) ^ t ∂residueMeasure B N h.val) =
        ∫ x : ℝ≥0, (x : ℝ) ^ t ∂residueMeasure B N h'.val) ∧
    coefficientProfile B N := by sorry

end MomentAmbiguitySecretary.Secretary
