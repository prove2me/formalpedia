-- Prove2me | Theorems.Thm_HunterPDE_Shared_normalJet_bound
-- name    : HunterPDE.Shared.normalJet_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T19:37:18.505973+00:00
-- url     : https://prove2.me/theorems/a70b6776-1fd6-498d-8ab0-494444b4ea39
-- title:
--   Uniform normal-coordinate power bound from vanishing boundary jets
-- statement:
--   Let $f$ be a smooth compactly supported real-valued function on Euclidean space. Fix a coordinate $i$ and a natural number $k$. If every pure normal derivative of order less than $k$ vanishes on $x_i=0$, there exists $C\ge0$ such that $$|f(x)|\le C|x_i|^k$$ for every $x$. The case $k=0$ is uniform boundedness. The estimate holds on both sides of the hyperplane.
-- source:
--   Derived calculus lemma, proved by induction using the normal segment and Mathlib norm_image_sub_le_of_norm_deriv_le_segment_01', https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/MeanValue.lean . The base case is compact-support boundedness. This is an independently stated supporting result for the boundary Taylor estimate, not a verbatim source theorem.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
open HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem HunterPDE.Shared.normalJet_bound {n : ℕ} (i : Fin n) (k : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f)
    (hb : ∀ r : ℕ, r < k → ∀ x : EuclideanSpace ℝ (Fin n), x i = 0 →
      iteratedPartial f (List.replicate r i) x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      ‖f x‖ ≤ C * ‖x i‖ ^ k := by sorry
