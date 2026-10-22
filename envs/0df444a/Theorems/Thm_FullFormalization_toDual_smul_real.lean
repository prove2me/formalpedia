-- Prove2me | Theorems.Thm_FullFormalization_toDual_smul_real
-- name    : FullFormalization.toDual_smul_real
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:34:40.628667+00:00
-- url     : https://prove2.me/theorems/53e07c6b-99c9-44cd-aabc-7a42673f2b1c
-- title:
--   ℝ-linearity of the Fréchet–Riesz identification toDual
-- statement:
--   Over a real inner product space the Fréchet–Riesz identification $\mathrm{toDual} : E \to E^*$, which sends a vector $z$ to the continuous linear functional $\langle z, \cdot\rangle$, is $\mathbb R$-linear:
--
--   $$\mathrm{toDual}\,(c \cdot z) = c \cdot \mathrm{toDual}\,z,$$
--
--   for every real scalar $c$ and every $z \in E$. Because the scalar field is $\mathbb R$, the conjugate appearing in the conjugate-linear identification is the identity, so the only obstruction is notational; the proof tests both sides against an arbitrary vector.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §19 and §32 (the scaling argument (32.1)) — this is an internal linearity fact used when transporting gradients along the scaling, and has no numbered source equation; Lean: FullFormalization.Scaling lines 127-134

-- Generated from F:/20261008/FullFormalization\FullFormalization\Scaling.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.Scaling

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, sections 19 and 32.

  Section 19 ("恢复一般 `L,R`", source lines 1638-1650 of the `### 19.` block) and
  section 32 (source lines 2688-2751) are the same argument in two places: starting
  from a *normalised* function `f_N` (optimiser `u`, initial point `0`, `L = R = 1`)
  one manufactures a general instance by

      f(x) = L R^2 f_N((x - x_init)/R)                                   (32.1)

  and the source records four consequences:

    (i)   ∇f(x) = L R ∇f_N((x - x_init)/R);
    (ii)  ‖∇f(x) - ∇f(y)‖ ≤ L ‖x - y‖                                 (L-smoothness);
    (iii) the optimiser is x⋆ = x_init + R u, at distance R from x_init;
    (iv)  "由于算法均按公开 R 在 normalized coordinates 中运行，归一化轨迹与
          L = R = 1 完全一致，所以所有 q_{A,N} 保持不变" — i.e. the *normalised*
          trajectory (and therefore every normalised loss `q_{A,N}`) is unchanged.

  Representation choices (recorded here because they are genuine formalisation
  decisions, not transcription):

  * `(x - x_init)/R` is written `(1/R) • (x - x_init)`.  Mathlib has no division
    `· / ·` of a vector by a scalar; `1/R` is the reciprocal *scalar* and the two
    expressions are identical field-theoretically.  No other mathematical content
    is hidden in this rewriting.

  * The source's claim (iii) `‖x⋆ - x_init‖ = R` is *not* a consequence of
    admissibility alone: `Admissible 1 1 fN 0 u` only supplies `‖u‖ ≤ 1`
    (this is exactly its `within_radius` field, since the normalized initial point
    is `0`).  What is proved here is the general identity
    `‖(x_init + R • u) - x_init‖ = R * ‖u‖` (`scaled_star_dist`) together with
    the specialisation `= R` under the extra hypothesis `‖u‖ = 1`
    (`scaled_star_dist_eq`).  For the extremisers used in the lower bounds of
    sections 20-31 one has `‖u‖ = 1`, so the source's sentence is recovered
    there; for a general admissible function it would be false (take `f_N = ‖·‖²`,
    `u = 0`).  This is recorded as a *precision* of the source, not a change of
    claim: the sentence is applied in the source only to the extremiser, whose
    `u` does satisfy `‖u‖ = 1`.

  * The transfer of `Admissible`/`AdmissibleUnique` (item (iii)) instantiates the
    admissible class with initial point `x_init` and optimiser `x_init + R • u`.
    Its `within_radius` field then reads `‖x_init - (x_init + R • u)‖ ≤ R`, which is
    exactly the normalised bound `‖u‖ ≤ 1` transported by the scaling — the
    radius hypothesis is *carried along* by the construction rather than added.

  * Item (iv) is formalised as an exact identity between the two trajectories
    (`nagX_scaled`, `nagY_scaled`) plus the exact invariance of the normalised
    loss (`normalizedLoss_scaled`, `normalizedLoss_scaled_nagX`).  This is the
    precise content of "every `q_{A,N}` is unchanged".
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_RationalNAG
import Definitions.Def_Scaling

open scoped Gradient

-- Several lemmas below are purely metric/affine and never use completeness of
-- `E` (which the section variable carries because `gradient` requires it).
set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 1.  The scaling map (32.1) -/





















/-! ## 2.  Gradient scaling (source line 2716)

`∇f(x) = L R ∇f_N((x - x_init)/R)`. -/













/-! ## 3.  Smoothness transfer (source line 2722)

`∀x y, ‖∇f(x) - ∇f(y)‖ ≤ L ‖x - y‖` whenever the normalised gradient is
1-Lipschitz. -/



/-! ## 4.  Differentiability and convexity transfer -/





/-! ## 5.  The optimiser is transported (source lines 2737-2747) -/











/-! ## 6.  Trajectory invariance (source line 2749)

"归一化轨迹与 `L = R = 1` 完全一致" — the scaled trajectory is the affine image of
the normalised one, `k ↦ x_init + R • (normalised iterate)`.  Consequently every
quantity computed on the normalised trajectory (in particular every `q_{A,N}`) is
unchanged. -/







/-! ## 7.  Invariance of the normalised loss `q_{A,N}` (source line 2749) -/







end FullFormalization

open FullFormalization

open scoped Gradient
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem FullFormalization.toDual_smul_real (c : ℝ) (z : E) :
    InnerProductSpace.toDual ℝ E (c • z) = c • InnerProductSpace.toDual ℝ E z := by sorry
