-- Prove2me | Theorems.Thm_HardyCausaloid_product_reconstruction
-- name    : HardyCausaloid.product_reconstruction
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T00:36:09.152649+00:00
-- url     : https://prove2.me/theorems/e8b668c7-0239-4bf9-9e76-dc5f1f37e230
-- title:
--   Single-site fiducial expansions reconstruct every entry of a finite regional table
-- statement:
--   Let a real-valued function of a finite family of labels admit a fixed linear reconstruction rule in each coordinate. Suppose that the weights on fiducial inputs are the corresponding coordinate unit vectors. For any full label assignment, its value equals the sum over the product of the finite fiducial sets of the product of the individual weights times the value at that fiducial assignment. This applies to elementary fiducial labels of an arbitrary finite region, including empty fiducial sets.
-- source:
--   Supporting finite-product lemma for Lucien Hardy, Towards Quantum Gravity, section 4.3, equations (28) and (29). https://arxiv.org/abs/gr-qc/0608043

import Mathlib
open Classical

namespace HardyCausaloid

open Classical in
theorem product_reconstruction {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    (Ω : ∀ i, Finset (A i)) (w : ∀ i, A i → Ω i → ℝ) (f : (∀ i, A i) → ℝ)
    (rep : ∀ α i, f α = ∑ k : Ω i, w i (α i) k * f (Function.update α i k.val))
    (unit : ∀ i (k j : Ω i), w i k.val j = if k = j then 1 else 0) :
    ∀ α, f α = ∑ l : ∀ i, Ω i, (∏ i, w i (α i) (l i)) * f (fun i => (l i).val) := by sorry

end HardyCausaloid
