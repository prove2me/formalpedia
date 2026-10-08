-- Prove2me | Theorems.Thm_MazurCampaign_rational_n_torsion_bound
-- name    : MazurCampaign.rational_n_torsion_bound
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T07:10:18.185985+00:00
-- url     : https://prove2.me/theorems/6cafc0f6-9094-478b-9369-0c770631618b
-- title:
--   Rational n-torsion is finite with at most n² elements
-- statement:
--   For any elliptic curve $E/\mathbb Q$ and any positive integer $n$, the subgroup of rational points annihilated by $n$ is finite and satisfies
--   $$\#E(\mathbb Q)[n]\le n^2,\qquad E(\mathbb Q)[n]=\{P\in E(\mathbb Q):nP=0\}.$$
--   No hypothesis on rank, reduction type, or the full torsion classification is assumed. This connects the geometric n-torsion theorem used in Anthropic's FLT formalization to the canonical rational-point group of the Mazur campaign. Its named downstream consumer excludes $(\mathbb Z/2\mathbb Z)^3$ from rational torsion. The theorem concerns a fixed n; finiteness of the union of all torsion subgroups is a separate result.
-- source:
--   Derived from https://prove2.me/theorems/11439a28-4f47-513e-b777-e6e7e1abad80 ; https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean ; Mathlib canonical injective base change on affine points.

import Definitions.Def_MazurCampaign_target_objects
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.SetTheory.Cardinal.NatCard
open scoped WeierstrassCurve.Affine

theorem MazurCampaign.rational_n_torsion_bound
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) (hn : n ≠ 0) :
    Finite (Submodule.torsionBy ℤ (E⁄ℚ).Point n) ∧
      Nat.card (Submodule.torsionBy ℤ (E⁄ℚ).Point n) ≤ n ^ 2 := by sorry
