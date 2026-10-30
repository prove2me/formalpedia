-- Prove2me | Theorems.Thm_NonRandomChoice_Assort_qip_mono_convex
-- name    : NonRandomChoice.Assort.qip_mono_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:35.269181+00:00
-- url     : https://prove2.me/theorems/c605cb57-4379-4316-b1ee-4cc139d04d82
-- title:
--   Proof of Theorem 5, p. 29 — q_{i′} is increasing and convex in q_0
-- statement:
--   Let $\Lambda>0$ and $h_\Lambda(y)=\Lambda(1-y)/(-\log y)$ for $0<y<1$, the no-purchase probability $q_0$ as a function of $q_{i'}=y$. The claim is that $q_{i'}$ is in turn an increasing convex function of $q_0$: there is a function $g$ with
--   $$g\bigl(h_\Lambda(y)\bigr)=y\quad\text{for all }0<y<1,$$
--   such that $g$ is increasing and convex on the range $h_\Lambda\bigl((0,1)\bigr)$ (in particular this range is an interval).
--
--   Together with the linear representation $q_i=(a_i/a_0)\,q_0$ for the other products, this is what places the choice model with a deterministic product utility under Lemma 1.
--
--   **Formalization Note** The inverse is stated as an existential $g$ that inverts $h_\Lambda$ on $(0,1)$, with `MonotoneOn` and `ConvexOn` on the image `qZeroOfQip Λ '' Set.Ioo 0 1`; `ConvexOn` includes convexity of that image. The page's range "$0<q_{i'}\le1$" is replaced by $0<q_{i'}<1$ for the reason given in the previous milestone. The image is not asserted to equal $(0,\Lambda)$.
-- source:
--   Wang, What Is the Impact of Non-Randomness on Random Choice Models?, SSRN 3579781 (PDF sha256 93af6c3d…), p. 29, proof of Theorem 5

import Mathlib
import Definitions.Def_NonRandomChoice_Assort_Model

namespace NonRandomChoice.Assort

theorem qip_mono_convex (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ g : ℝ → ℝ, (∀ y ∈ Set.Ioo (0 : ℝ) 1, g (qZeroOfQip Λ y) = y) ∧
      MonotoneOn g (qZeroOfQip Λ '' Set.Ioo 0 1) ∧
      ConvexOn ℝ (qZeroOfQip Λ '' Set.Ioo 0 1) g := by sorry

end NonRandomChoice.Assort
