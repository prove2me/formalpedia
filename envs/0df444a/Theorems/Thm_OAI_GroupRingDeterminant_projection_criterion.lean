-- Prove2me | Theorems.Thm_OAI_GroupRingDeterminant_projection_criterion
-- name    : OAI.GroupRingDeterminant.projection_criterion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T20:04:14.789797+00:00
-- url     : https://prove2.me/theorems/b7b460f4-ba6f-45ae-94fb-7b54b1f50ef1
-- title:
--   A rational projection with an odd-denominator integral form that factors mod 2 through fewer coordinates than its trace yields a counterexample to the group-ring determinant conjecture (OpenAI)
-- statement:
--   Let $G$ be a finitely generated group (`G : Type` with `[Group G]` and `[Group.FG G]`), and let $r$ and $m$ be finite index types with decidable equality (`[Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m]`), $r$ nonempty (`[Nonempty r]`). Write $\mathbb{Q}[G]$, $\mathbb{Z}[G]$ and $\mathbb{F}_2[G]$ for the group rings `MonoidAlgebra ℚ G`, `MonoidAlgebra ℤ G` and `MonoidAlgebra (ZMod 2) G`. For an element $a$ of a group ring, `a.coeff 1` is its coefficient at the identity. Here `toRat : ℤ[G] → ℚ[G]` and `toMod 2 : ℤ[G] → 𝔽₂[G]` are the coefficientwise ring maps, and `Z.map f` applies $f$ to every entry of a matrix. Assume:
--
--   1. (`hodd`) $D$ is an odd natural number;
--   2. (`hP`) $P$ is an $m \times m$ matrix over $\mathbb{Q}[G]$ with $P^2 = P$ and $P$ self-adjoint (`IsSelfAdjoint P`: $P$ equals its conjugate transpose, where the star of a group-ring element is $\sum_g a_g\, g \mapsto \sum_g \overline{a_g}\, g^{-1}$, the instance `groupAlgebraStar`);
--   3. (`htrace`) $|r| < \sum_{i \in m} (P_{ii})_1$, where $(P_{ii})_1$ is `(P i i).coeff 1`;
--   4. (`hZ`) $Z$ is an $m \times m$ matrix over $\mathbb{Z}[G]$ whose image in $\mathbb{Q}[G]$ is $D \cdot P$;
--   5. (`huv`) $u$ ($m \times r$) and $v$ ($r \times m$) are matrices over $\mathbb{F}_2[G]$ with $u v$ equal to the reduction of $Z$ modulo $2$.
--
--   Then `MainStatement` holds: there are a finitely generated group $G'$, an $n \ge 1$, an $n \times n$ matrix $A$ over $\mathbb{Z}[G']$ and a bounded operator $T$ on $\ell^2(G')^n$ such that $A$ is invertible over $\mathbb{Q}[G']$ (`IsUnit (rationalMatrix A)`), $T$ is the left-regular operator of $A$ (`IsRegularOperator A T`), $T$ is invertible, and its Fuglede–Kadison determinant satisfies $0 < \mathrm{fkDet}(T) < 1$. The definitions `MainStatement`, `IsRegularOperator`, `rationalMatrix`, `fkDet` and `Hilbert` are those of the published bundle `Def_GroupRingDeterminant`.
--
--   Lean: `OAI.GroupRingDeterminant.projection_criterion`, OpenAI's theorem of that name in `lean/OAI/Analysis/GroupDeterminants/ProjectionCriterion.lean`; `toRat` and `toMod` and the group-ring star structure come from the definitions bundle `OAIQWGRD000` of this split.
-- source:
--   OpenAI, A Counterexample to the Group-Ring Determinant Conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 197; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Counterexample-to-the-Group-Ring-Determinant-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/GroupDeterminants/ProjectionCriterion.lean (declaration OAI.GroupRingDeterminant.projection_criterion)

import Mathlib
import Definitions.Def_GroupRingDeterminant
import Definitions.Def_OAIQWGRD000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section ProjectionCriterion
variable {G r m : Type} [Group G] [Group.FG G]
variable [Fintype r] [Fintype m] [DecidableEq r] [DecidableEq m] [Nonempty r]

theorem projection_criterion (D : ℕ) (hodd : Odd D)
    (P : Matrix m m (MonoidAlgebra ℚ G)) (hP : P * P = P ∧ IsSelfAdjoint P)
    (htrace : (Fintype.card r : ℚ) < ∑ i, (P i i).coeff 1)
    (Z : Matrix m m (MonoidAlgebra ℤ G)) (hZ : Z.map toRat = (D : ℚ) • P)
    (u : Matrix m r (MonoidAlgebra (ZMod 2) G))
    (v : Matrix r m (MonoidAlgebra (ZMod 2) G)) (huv : u * v = Z.map (toMod 2)) :
    MainStatement := by
  sorry

end ProjectionCriterion
end GroupRingDeterminant

end

end OAI
end
