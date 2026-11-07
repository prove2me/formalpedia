-- Prove2me | Theorems.Thm_FreeSpencer_lemma_7_6
-- name    : FreeSpencer.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:10:21.071752+00:00
-- url     : https://prove2.me/theorems/f75f19bb-05ae-4bba-8f85-11f723f079b5
-- title:
--   Lemma 7.6, p.53 — moment bounds for the stopped trial
-- statement:
--   Assume (7.2), (7.3) and the properties of the procedures. At the terminal state of a trial from a saved state with $\ell\ge32$ live coordinates,
--   $$\mathbb E\Bigl[\Psi+\frac{2048}{\sqrt\ell}a\Bigr]\le3.0001\sqrt\ell,\qquad\mathbb EM_*^2\le\ell\tau,$$
--   and with probability greater than $1/2$,
--   $$d\le\ell/32,\quad\Psi\le8\sqrt\ell,\quad M_*\le1.5\sqrt\ell.$$
--   This makes acceptance likely, although individual moves may raise the potential.
--
--   Differences from the source:
--   - generalization: the procedures of Algorithms 2 and 3 → every Procs with Procs.Spec; reason: Section 7.2 and Proposition 7.9 are stated for "the properties of the procedures"; the implemented procedures are one instance
--   - reading: "The total trace of discarded small eigenvalues is at most ℓ/1024" (p.50); the basis of W (p.50) → per call u ≤ 2δ(rank C − rank C′), and the App. F form of the basis: ½P_W ⪯ C, W ⊆ V, dim W ≥ 2 Tr C − rank C − |F| − 1; reason: these are what Lemma C.2, Lemma 7.1, Remark 7.2 and App. F.4 provide; the total follows, since the covariance range never grows
--   - encoding: C on ℝ^{I₀}, starting at I_ℓ → C on ℝⁿ, starting at the diagonal projection on I₀; reason: Remark 7.2 (p.49): all n coordinates may be kept; the zero rows do not change η_C
--   - encoding: expectation and probability at the terminal state → finite sums written as tsum over the state type, and PMF.toOuterMeasure; reason: the law has finite support
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 7.6, p.53; proof pp.53–54

import Mathlib
import Definitions.Def_FreeSpencer_trialLaw
import Definitions.Def_FreeSpencer_Hyp72
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Lemma 7.6** (Moment bounds for the stopped trial), (7.12) and (7.13), under the law of the terminal
state, assuming (7.2) and (7.3) for the mode. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 7.6, p.53; proof pp.53–54.

**Formalization Note** The law has finite support, so the expectations are finite sums written as `tsum`
over the state type. `a` is the cut loss only, and `d = a + u` (p.52). The bound `M₄` of Theorem D.1
enters through `h`, as on the page. -/
theorem lemma_7_6 {n m : ℕ} (hn : 32 ≤ n) (hm : 1 ≤ m) (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (hsymm : ∀ i, (A i).IsSymm) (hA : ∀ i, ‖A i‖ ≤ 1) (P : Procs n m)
    (hP : P.Spec A (params n m)) (xs : Fin n → ℝ) (hxs : SavedOK xs)
    (h72 : Hyp72 A (params n m)) (h73 : Hyp73 A (params n m)) :
    let par := params n m
    let ℓ : ℝ := ((liveSet xs).card : ℝ)
    let μ := trialLaw P A par xs
    ∑' s, (μ s).toReal * (trialPsi A par xs s + 2048 / Real.sqrt ℓ * s.a) ≤ 3.0001 * Real.sqrt ℓ ∧
    ∑' s, (μ s).toReal * trialMart A par xs s ^ 2 ≤ ℓ * par.τ ∧
    (1 / 2 : ENNReal) < μ.toOuterMeasure {s | s.a + s.u ≤ ℓ / 32 ∧
      trialPsi A par xs s ≤ 8 * Real.sqrt ℓ ∧ trialMart A par xs s ≤ 1.5 * Real.sqrt ℓ} := by sorry

end FreeSpencer
