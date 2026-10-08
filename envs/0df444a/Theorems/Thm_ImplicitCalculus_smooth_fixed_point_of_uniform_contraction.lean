-- Prove2me | Theorems.Thm_ImplicitCalculus_smooth_fixed_point_of_uniform_contraction
-- name    : ImplicitCalculus.smooth_fixed_point_of_uniform_contraction
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T22:00:30.332561+00:00
-- url     : https://prove2.me/theorems/a55ac7f7-85df-45bd-b152-4b88060b7199
-- title:
--   Smooth parameter dependence of fixed points of uniform contractions
-- statement:
--   Let P and V be real Banach spaces and Φ:P×V→V a smooth map. Suppose every map z↦Φ(p,z) is Lipschitz with the same constant K<1. Let r:P→V be any family of fixed points, so Φ(p,r(p))=r(p) for every p. Then r is smooth. Continuity of r is not an assumption: it follows from the contraction estimate. Existence of the fixed points is supplied by the family r; the theorem establishes their regularity.
-- source:
--   Parameterized contraction principle and implicit function theorem. Independent Banach-space lemma for the Picard integral-operator route to smooth flow dependence; related to the integration stage of Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, Theorem 2.20, pp. 14–15. Uses the independently Proved ImplicitCalculus.contDiffAt_continuous_solution, Lipschitz derivative estimates and Units.oneSub at Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_ImplicitCalculus_contDiffAt_continuous_solution
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Linarith

open Filter
open scoped Topology ContDiff NNReal
set_option autoImplicit false

theorem ImplicitCalculus.smooth_fixed_point_of_uniform_contraction
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (Φ : P × V → V) (hΦ : ContDiff ℝ ∞ Φ)
    (K : ℝ≥0) (hK : K < 1)
    (hLip : ∀ p, LipschitzWith K (fun z => Φ (p,z)))
    (r : P → V) (hr : ∀ p, Φ (p,r p) = r p) : ContDiff ℝ ∞ r := by sorry
