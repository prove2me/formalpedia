-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_isRepOf_baseMass_le_heightForm
-- name    : ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/7c8b86d1-e8a1-5b2f-b734-b3339ae19983
-- title:
--   Height form dominates base mass on suitable representatives
-- statement:
--   Fix a natural number $N \neq 0$, an intermediate field $K$ of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ that is finite over $\mathbb{Q}$, a natural number $g'$, and a family $s : \mathrm{Fin}\,r \to$ `modularFunctionFieldBar N` which is an embedding basis in the sense of `IsEmbBasis`, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its span is the Riemann–Roch space $L(\,$`embDivisor N`$\,)$, together with a real $\mu > 0$. Then there are reals $\eta, C$ with $\eta > 0$, depending only on these data, such that the following holds for every class $c$ in the subgroup of $\mathrm{Pic}^0$ of `modularFunctionFieldBar N` fixed by the subgroup of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing $K$ pointwise, and every divisor $D$: if $D$ represents $c$ in the sense of `IsRepOf`, that is, $D$ is effective, $D = E + g'\cdot(\,$`cuspInftyBar N`$\,)$ for a degree-zero divisor $E$ whose class is $c$, and $D$ is invariant under the arithmetic Galois action of every $\sigma$ fixing $K$, and if the genus `genusFF` is at most $\mu\,(\,$`offBaseMass N D`$- 1)$, where the off-base mass is the sum of the multiplicities of $D$ away from the cusp, then some divisor $D_2$ also represents $c$ in this sense and satisfies $\eta \cdot$ `baseMass N s D₂` $- C \le$ `heightForm N s D₂`, the base mass being the sum over places $v \neq$ `cuspInftyBar N` of $D_2(v)\cdot$ `baseHt s (cuspInftyBar N) v`.
--
--   This is the lower-bound step in the construction of a height on the degree-zero divisor class group of the modular curve: among Galois-stable effective representatives of a class whose off-cusp mass is large relative to the genus, one can always find one on which the quadratic height form dominates a positive multiple of the base-height-weighted mass up to an additive constant, with $\eta$ and $C$ uniform in the class. It is used by [`ModularCurve.JZero.exists_isRepOf_heightForm_lower`](thm.html#ModularCurve.JZero.exists_isRepOf_heightForm_lower).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_isRepOf_baseMass_le_heightForm.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (g' : ℕ) {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (μ : ℝ) (hμ : 0 < μ) :
    ∃ η C : ℝ, 0 < η ∧
      ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        IsRepOf N K g' c D →
        (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
          ≤ μ * ((offBaseMass N D : ℝ) - 1) →
        ∃ D₂, IsRepOf N K g' c D₂ ∧
          η * baseMass N s D₂ - C ≤ heightForm N s D₂ := by sorry
