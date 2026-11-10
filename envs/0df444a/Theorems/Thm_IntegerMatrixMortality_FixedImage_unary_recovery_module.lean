-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_unary_recovery_module
-- name    : IntegerMatrixMortality.FixedImage.unary_recovery_module
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:05.333012+00:00
-- url     : https://prove2.me/theorems/79e49dd5-682a-4710-9b9f-0f1afd54e53d
-- title:
--   Proposition D.4 — Unary recovery module
-- statement:
--   Let p≥7 be prime, m∈{2,3} and a∈ℕ. The recovery graph (D.8) has a valid path from its entry to its exit on input X_{a,m(a+1)−1}, and every such completing path has output
--
--   $$X_{a,m(a+1)-1}\longmapsto z_{m(a+1)-1}.$$
--
--   It has exactly 4m+2 listed generators. After a private allocation of its phases below N and a global choice p>6N, the same output assertion holds for unrestricted words, stopped at their first arrival at the exit. The formal statement allows additional guarded generators whose sources avoid every private recovery phase, so it applies to the whole compiled family rather than only intended graph traversals.
--
--   Differences from the source:
--   - encoding: distinct private recovery phases and first arrival at the exit → injective phase labels, explicit source-avoidance, and residue-block first arrival for actual words; reason: the hypotheses express the source private allocation and global p>6N convention
--   - generalization: the globally compiled instruction family → any additional guarded generators whose sources avoid the private recovery phases; reason: the source compiled family satisfies this privacy condition; no correctness assumption is needed for other modules before first exit
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Proposition D.4, PDF p. 29 / printed p. 27

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem unary_recovery_module
    (p m a : ℕ) (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hm : m ∈ ({2,3} : Finset ℕ)) :
      let M := recoveryModule m
      let x := some (intermediateCode p a (m*(a+1)-1))
      let y := some (unaryCode p (m*(a+1)-1))
      Completes p M x y ∧ (∀ z, Completes p M x z → z = y) ∧
      M.edges.length = 4*m+2 ∧
      (∀ (label : ℕ → ℕ) (N : ℕ) (other : List GeneratorEdge),
        Function.Injective label → 6*N < p →
        (∀ e ∈ (renameModule M label).edges ++ other,
          e.source < N ∧ e.target < N ∧ e.digit ∈ delta) →
        (∀ e ∈ other, ∀ s ∈ M.edges.map GeneratorEdge.source,
          s ≠ M.exit → e.source ≠ label s) →
        ∀ w : List ZMat,
          (∀ A ∈ w, ∃ e ∈ (renameModule M label).edges ++ other, A = edgeMatrix p e) →
          FirstPhaseArrival p (label M.exit) w (shift (label M.entry) x) →
          InPhase p (label M.exit)
            (projectiveAction (rationalMatrix (wordMatrix w)) (shift (label M.entry) x)) →
          projectiveAction (rationalMatrix (wordMatrix w)) (shift (label M.entry) x) =
            shift (label M.exit) y) := by sorry

end IntegerMatrixMortality.FixedImage
