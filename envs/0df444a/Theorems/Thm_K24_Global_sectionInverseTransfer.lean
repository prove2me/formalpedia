-- Prove2me | Theorems.Thm_K24_Global_sectionInverseTransfer
-- name    : K24.Global.sectionInverseTransfer
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T18:47:27.024676+00:00
-- url     : https://prove2.me/theorems/c81572c5-7720-44c3-8b82-b68221d7f050
-- title:
--   K24: inverse transfer and dual gap on the actual concrete section spaces
-- statement:
--   Let `X` and `Y` be real vector spaces and let `S ⊆ X`, `T ⊆ Y` be the actual admissible section sets, equipped with extended norm functions `nx` and `ny`. Suppose these sets and norms satisfy the canonical `SectionBanachSpace` laws, including finiteness on the admissible sections and completeness. Let `A, B : X → Y` be the given maps, and let `CA` be a positive finite nonnegative-real constant.
--
--   Assume that the restriction of `A` to `S` is a bounded linear bijection onto `T`, and that every `u ∈ S` satisfies `nx u ≤ CA · ny (A u)`. Assume the actual difference `u ↦ B u − A u` maps `S` into `T`, is linear on `S`, and is bounded in the indicated section norms. Define its operator norm by the canonical infimum over all valid extended norm bounds. If `CA` times this operator norm is less than `1/2`, then:
--
--   - The restriction of the original map `B` is a bounded linear bijection from `S` onto `T`.
--   - Every `u ∈ S` satisfies `nx u ≤ 2 CA · ny (B u)`.
--   - For every bounded linear real functional `phi` on `T`, its canonical operator norm is at most `2 CA` times the canonical operator norm of the actual composition `phi ∘ B` on `S`.
--
--   The theorem permits zero-dimensional section spaces. It requires no norm or topology on the full raw section modules, and makes no assertion about map values or norm finiteness outside the admissible sets.
--
--   This is the concrete section-space realization of K24 §4, equations (4.1)–(4.3) and the following adjoint-gap assertion. It supplies the common inverse-transfer step for the natural tensor Hölder pair, natural vector Hölder pair, shifted vector Hölder pair, and tensor Sobolev pair once their actual Banach and perturbation hypotheses are established. It does not itself establish those geometric regularity hypotheses or the other components of the full K24 statement.
--
--   Supporting original full target https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §4 equations (4.1)–(4.3) and the adjoint-gap assertion; concrete canonical section predicates in definition 738f77a5-d72a-4017-95ce-870ad72cb8a2.

import Definitions.Def_K24GlobalAnalysis
set_option autoImplicit false
open scoped NNReal ENNReal
universe u v

theorem K24.Global.sectionInverseTransfer :
  ∀ {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞},
    K24.Global.SectionBanachSpace S nx →
    K24.Global.SectionBanachSpace T ny →
    ∀ (A B : X → Y) (CA : ℝ≥0), 0 < CA →
    K24.Global.SectionIsomorphism S T nx ny A →
    K24.Global.SectionInverseBound S nx ny A CA →
    Set.MapsTo (fun u => B u - A u) S T →
    K24.Global.SectionLinearOn S (fun u => B u - A u) →
    K24.Global.SectionBoundedOn S nx ny (fun u => B u - A u) →
    (CA : ℝ≥0∞) * K24.Global.sectionOperatorENorm S nx ny (fun u => B u - A u)
      < (1 / 2 : ℝ≥0∞) →
    K24.Global.SectionIsomorphism S T nx ny B ∧
    K24.Global.SectionInverseBound S nx ny B (2 * CA) ∧
    K24.Global.SectionDualGap S T nx ny B (2 * CA) := by sorry
