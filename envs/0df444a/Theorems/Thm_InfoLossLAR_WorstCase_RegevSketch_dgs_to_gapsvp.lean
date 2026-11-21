-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_to_gapsvp
-- name    : InfoLossLAR.WorstCase.RegevSketch.dgs_to_gapsvp
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:14:32.987351+00:00
-- url     : https://prove2.me/theorems/befd1eb1-eff7-48ab-a6ae-417d25d7870d
-- title:
--   Uniform GapSVP from a concrete joint DGS sampler
-- statement:
--   There are absolute natural numbers $C,k$, with $C\ge1$, with the following property. For every uniform multi-output quantum polynomial-time family $G$ and every negligible function $\delta$, there are a uniform quantum polynomial-time decision algorithm $A$ and a cutoff such that, at every positive dimension $n$ beyond the cutoff,
--
--   $$
--   \mathrm{DGSAt}(G,n,\delta(n))
--   \ \Longrightarrow\
--   A\text{ solves }\mathrm{GapSVP}_{Cq(n)(\log_2(n+2))^k}.
--   $$
--
--   The guarantee is the published worst-case promise decision requirement on every nonsingular integer basis and every positive rational threshold. The constants precede the sampler and error function.
--
--   This branch includes the external promise-problem reduction and verifier used by the source's GapSVP argument. A collection of short lattice vectors does not itself discharge this decision-algorithm obligation.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Lemma 3.20 and its preceding reduction from GapSVP to the promise GapCVP variant, full-version PDF p. 30; fixed-family substitution and explicit uniform decision algorithm.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem dgs_to_gapsvp :
  ∃ C k : ℕ,1 ≤ C ∧ ∀ G : MFamily,IsMQPT G →
    ∀ error : ℕ → ℝ,Negligible error →
      ∃ A : Family,IsQPT A ∧ ∃ cutoff : ℕ,∀ n ≥ cutoff,1 ≤ n →
        DGSAt G n (error n) →
          SolvesGapSVP A (famN n) ((C : ℝ)*(famq n : ℝ)*Real.logb 2 ((n : ℝ)+2)^k) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
