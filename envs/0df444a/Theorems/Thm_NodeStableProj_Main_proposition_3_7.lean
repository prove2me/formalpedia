-- Prove2me | Theorems.Thm_NodeStableProj_Main_proposition_3_7
-- name    : NodeStableProj.Main.proposition_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:58:15.353928+00:00
-- url     : https://prove2.me/theorems/00d76cab-84a7-4a4f-9f3b-475fee39a284
-- title:
--   Proposition 3.7 (Corollary 5.5 in [HSV26]) — concurrent s-sparse composition of (ε̃, 0)-DP continual-release mechanisms
-- statement:
--   Let $\{\mathcal M_j\}$ be interactive mechanisms, each $(\tilde\varepsilon,0)$-differentially private in the continual-release model with adaptive inputs, and let the adversary $\mathcal A$ and the identifier $\mathcal I$ define a concurrent $s$-sparse composition of them. Then
--   $$\mathcal A*\mathcal I[0]*\{\mathcal M_j\}\ \approx_{\varepsilon,\delta'}\ \mathcal A*\mathcal I[1]*\{\mathcal M_j\}$$
--   (a) for every pair $(\varepsilon,\delta')$ that is valid for the standard noninteractive composition of $s$ mechanisms that are $(\tilde\varepsilon,0)$-differentially private, and (b) in particular, for every $\delta'>0$, with
--   $$\varepsilon=\tilde\varepsilon\sqrt{2s\ln(1/\delta')}+s\,\tilde\varepsilon\,\frac{e^{\tilde\varepsilon}-1}{e^{\tilde\varepsilon}+1}.$$
--
--   The point is that the leakage depends on the sparsity $s$ only, not on the number of mechanisms or steps; Lemma 3.3 applies it with $s=\hat D$ to the $n-1$ detectors.
--
--   Differences from the source:
--   - generalization: mechanisms {M_j}_{j∈N} → mechanisms indexed by an arbitrary type J with decidable equality; reason: J = ℕ is a special case; Claim 3.8 indexes the detectors by V \ {v*}
--   - reading: "privacy parameters that apply to the standard, noninteractive composition of s mechanisms that are (ε̃, 0)-DP" → NonInteractiveComposition s ε̃ ε δ': for all s pairs of probability laws on arbitrary spaces with P_i ≈_{ε̃,0} Q_i, ⊗P_i ≈_{ε,δ'} ⊗Q_i; reason: the standard meaning of a composition bound for s (ε̃,0)-DP mechanisms
--   - encoding: randomized interactive mechanisms and adversary with private randomness and state → responses and queries are functions of an independent uniform tape and the history; common message and output types; the output must be measurable; reason: a stateful randomized process is a function of its randomness and its inputs so far
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 16, Proposition 3.7 (Corollary 5.5 in [HSV26])

import Mathlib
import Definitions.Def_NodeStableProj_Main_Concurrent

open MeasureTheory

namespace NodeStableProj.Main

/-- Proposition 3.7 (Corollary 5.5 in [HSV26]), p. 16: if `A, I` define an `s`-sparse
composition of mechanisms that are each `(ε̃, 0)`-DP in the continual-release model with adaptive
inputs, then `A ∗ I[0] ∗ {M_j} ≈_{ε,δ'} A ∗ I[1] ∗ {M_j}` for every `(ε, δ')` valid for the
noninteractive composition of `s` `(ε̃, 0)`-DP mechanisms; in particular for
`ε = ε̃ √(2 s ln(1/δ')) + s ε̃ (e^{ε̃} − 1)/(e^{ε̃} + 1)` and any `δ' > 0`. -/
theorem proposition_3_7 {J X Y Z : Type} [DecidableEq J] [MeasurableSpace Z]
    (M : J → Mechanism X Y) (A : Adversary J X Y Z) (s : ℕ) (εt : ℝ)
    (hDP : ∀ j, IsContinualDP (M j) εt) (hA : IsSparseComposition M A s) :
    (∀ ε δ' : ℝ, NonInteractiveComposition s εt ε δ' →
      PFRelease.Indist (compositionLaw M A false) (compositionLaw M A true) ε δ') ∧
    (∀ δ' : ℝ, 0 < δ' →
      PFRelease.Indist (compositionLaw M A false) (compositionLaw M A true)
        (εt * Real.sqrt (2 * s * Real.log (1 / δ')) +
          s * εt * (Real.exp εt - 1) / (Real.exp εt + 1)) δ') := by sorry

end NodeStableProj.Main
