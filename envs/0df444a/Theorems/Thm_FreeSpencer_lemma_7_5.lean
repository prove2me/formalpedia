-- Prove2me | Theorems.Thm_FreeSpencer_lemma_7_5
-- name    : FreeSpencer.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:10:19.847232+00:00
-- url     : https://prove2.me/theorems/74195e26-7b84-42a5-bba3-a2f0fe2f05aa
-- title:
--   Lemma 7.5, p.52 — invariant and terminal alternatives
-- statement:
--   For $n\ge32$, $m\ge1$, procedures with the properties of Section 7.2 and a saved state with at least $32$ live coordinates, every state of Algorithm 2 is in the cube and preserves frozen signs, and with $\ell$ the initial live count and $T$ the clock,
--   $$\mathrm{Tr}\,C+a+u+v=\ell,\quad17\ell T/64\le v\le\ell T,\quad u\le\ell/1024,\quad r_c\le a_0\ell,$$
--   $$\|x\|_2^2\ge\|x_*\|_2^2+v,\quad\|x-x_*-y\|_1\le r_c.$$
--   Before each movement, $\mathrm{Tr}\,Q\ge17\ell/64>0$. A trial has at most $\lfloor\tau/h^2\rfloor$ movements. If it terminates with $d\le\ell/32$, then either at least $\ell/8$ new coordinates have frozen, or $T>\tau-h^2\ge0.99\tau$. The progress of the walk therefore holds on every path.
--
--   Differences from the source:
--   - generalization: the procedures of Algorithms 2 and 3 → every Procs with Procs.Spec; reason: Section 7.2 and Proposition 7.9 are stated for "the properties of the procedures"; the implemented procedures are one instance
--   - reading: "The total trace of discarded small eigenvalues is at most ℓ/1024" (p.50); the basis of W (p.50) → per call u ≤ 2δ(rank C − rank C′), and the App. F form of the basis: ½P_W ⪯ C, W ⊆ V, dim W ≥ 2 Tr C − rank C − |F| − 1; reason: these are what Lemma C.2, Lemma 7.1, Remark 7.2 and App. F.4 provide; the total follows, since the covariance range never grows
--   - encoding: C on ℝ^{I₀}, starting at I_ℓ → C on ℝⁿ, starting at the diagonal projection on I₀; reason: Remark 7.2 (p.49): all n coordinates may be kept; the zero rows do not change η_C
--   - encoding: "every state", the clock T → the support of the law after any number of passes; T = moves · h²; reason: the same states
--   - reading: Lemma 7.5 at the input n, m ≥ 1 of Section 7.2 → n ≥ 32, m ≥ 1 with ℓ ≥ 32 live coordinates; reason: p.77: parameters are computed for n ≥ 32; p.50: a trial retains ℓ ≥ 32 coordinates
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 7.5, p.52; proof pp.52–53

import Mathlib
import Definitions.Def_FreeSpencer_trialLaw
import Definitions.Def_FreeSpencer_Hyp72
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Lemma 7.5** (Invariant and terminal alternatives), on every reachable state of Algorithm 2, for every
procedures with the properties of Section 7.2. Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Lemma 7.5, p.52; proof pp.52–53.

**Formalization Note** "Every state" is the support of the law after any number of passes. `T` is
`moves · h²`; "at most `⌊τ/h²⌋` movements" is `moves ≤ ⌊τ/h²⌋`. All `n` coordinates are kept in the
coefficient space and `C` starts at the identity on `I₀` (Remark 7.2). "Preserves frozen signs" is the
pair of clauses on coordinates outside `I₀` and on the step from `s` to `s'`. -/
theorem lemma_7_5 {n m : ℕ} (hn : 32 ≤ n) (hm : 1 ≤ m) (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (hsymm : ∀ i, (A i).IsSymm) (hA : ∀ i, ‖A i‖ ≤ 1) (P : Procs n m)
    (hP : P.Spec A (params n m)) (xs : Fin n → ℝ) (hxs : SavedOK xs) :
    let par := params n m
    let ℓ : ℝ := ((liveSet xs).card : ℝ)
    let h := stepH n m par
    (∀ (k : ℕ) (s : TrialState n), s ∈ (trialIter P A par xs k).support →
      (∀ i, |s.x i| ≤ 1) ∧ (∀ i, i ∉ liveSet xs → s.x i = xs i) ∧ (∀ i ∈ s.F, |s.x i| = 1) ∧
      (∀ s' ∈ (trialStep P A par xs s).support, s.F ⊆ s'.F ∧ ∀ i ∈ s.F, s'.x i = s.x i) ∧
      Matrix.trace s.C + s.a + s.u + s.v = ℓ ∧
      17 * ℓ * ((s.moves : ℝ) * h ^ 2) / 64 ≤ s.v ∧ s.v ≤ ℓ * ((s.moves : ℝ) * h ^ 2) ∧
      s.u ≤ ℓ / 1024 ∧ s.rc ≤ marginA n * ℓ ∧
      xs ⬝ᵥ xs + s.v ≤ s.x ⬝ᵥ s.x ∧ ∑ i, |s.x i - xs i - s.y i| ≤ s.rc ∧
      s.moves ≤ ⌊par.τ / h ^ 2⌋₊ ∧
      (s.stopped = false → (s.moves : ℝ) * h ^ 2 + h ^ 2 ≤ par.τ → (s.F.card : ℝ) < ℓ / 8 →
        s.a + s.u ≤ ℓ / 32 →
        let r := P.prep (liveSet xs).card (s.a + s.u) (center A s.x) s.C
        s.a + r.2.1 + (s.u + r.2.2) ≤ ℓ / 32 →
        17 * ℓ / 64 ≤ Matrix.trace (moveCov (P.basis r.1 s.x s.F)) ∧ 0 < Matrix.trace (moveCov (P.basis r.1 s.x s.F)))) ∧
    (∀ s ∈ (trialLaw P A par xs).support, s.stopped = true ∧
      (s.a + s.u ≤ ℓ / 32 → ℓ / 8 ≤ (s.F.card : ℝ) ∨
        (par.τ - h ^ 2 < (s.moves : ℝ) * h ^ 2 ∧ 0.99 * par.τ ≤ par.τ - h ^ 2))) := by sorry

end FreeSpencer
