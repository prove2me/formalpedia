-- Prove2me | Theorems.Thm_HigherOrderId_Certify_eq_84_87
-- name    : HigherOrderId.Certify.eq_84_87
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:19:13.855059+00:00
-- url     : https://prove2.me/theorems/852b46cc-f6f5-409d-a46a-1ac8680a130c
-- title:
--   §B.5, Eqs. (84)–(87) — for m ≥ 6, ≥ m²/4 singular values a_j ≤ 1/2 carry orthogonal zero-diagonal directions Q_j with ‖Q_j‖² ∈ [1, 4/3] and Σ_I a_j^{-2} ≥ ℓ³/m²
-- statement:
--   Let $d\ge10$, $m\ge6$, let $U\in\mathbb R^{d\times m}$ have orthonormal columns, and let $D_U$ have full column rank with singular values $a_j$. Then at most $2m$ of the $a_j$ exceed $1/2$, and there is an index set $I$ with
--   $$\ell:=|I|\ge t-2m\ge\frac{m^2}4,\qquad a_j\le\tfrac12\ (j\in I).\tag{84}$$
--   For every such $I$ and every choice of orthonormal right and left singular vectors $B_j\in\mathrm{Sym}_m$, $y_j\in\mathbb R^d$ ($D_U(B_j)=a_jy_j$, $D_U^*(y_j)=a_jB_j$, $j\in I$):
--
--   - $y_j$ is an eigenvector of $D_{\mathrm{rest}}D_{\mathrm{rest}}^*$ with eigenvalue $1-a_j^2$;
--   - $r_j=-\frac{a_j}{1-a_j^2}D_{\mathrm{rest}}^*y_j$ is the minimum-norm rest block with $D_{\mathrm{rest}}(r_j)=-a_jy_j$, and $\|r_j\|_F^2=a_j^2/(1-a_j^2)$ (85);
--   - the matrices $Q_j=UB_jU^\top+r_j$ (86) have zero diagonal, are mutually Frobenius-orthogonal, satisfy $\|Q_j\|_F^2=(1-a_j^2)^{-1}\in[1,4/3]$, and their rest components $r_j$ are mutually orthogonal;
--   - $\frac1\ell\sum_{j\in I}a_j^{-2}\ge\big(\frac1\ell\sum_{j\in I}a_j\big)^{-2}$, $\sum_{j\in I}a_j\le\sum_ja_j\le m$, and, with a universal constant $c>0$,
--   $$\sum_{j\in I}a_j^{-2}\ge\frac{\ell^3}{(\sum_{j\in I}a_j)^2}\ge\frac{\ell^3}{m^2}\ge c\,m^4.\tag{87}$$
--
--   These directions realize the inverse-spectrum lower bound as valid zero-diagonal mechanism directions, which feed the testing lower bound of Theorem 5.2.
--
--   Differences from the source:
--   - encoding: "Let B_j and y_j be corresponding orthonormal right and left singular vectors" → for every family (B_j, y_j)_{j ∈ I} with B_j symmetric, Frobenius-orthonormal, y_j orthonormal, D_U(B_j) = a_j y_j and D_U*(y_j) = a_j B_j; reason: the statements hold for any choice of singular vectors
--   - reading: (85)–(87) for "an index set I" with (84) → for every index set I with |I| ≥ t − 2m and a_j ≤ 1/2 on I; reason: the text uses an arbitrary such I
--   - encoding: rest blocks r ∈ R_{U,V_env}; D_rest* → symmetric r with Uᵀ r U = 0; D_rest*(y) = Diag(y) − UUᵀDiag(y)UUᵀ; reason: the orthogonal complement of {UBUᵀ} in Sym_d, and the orthogonal projection of D*(y) = Diag(y) onto it
--   - encoding: ≳ m⁴ → ∃ universal c > 0 (before d, m, U) with ℓ³/m² ≥ c m⁴; reason: explicit form of ≳
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 27, §B.5, Eqs. (84)–(87) (PDF p. 28)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Completion
import Definitions.Def_HigherOrderId_Certify_TallCompletion

open Matrix

namespace HigherOrderId.Certify

/-- §B.5, Eqs. (84)–(87) (zero-diagonal directions realizing the inverse spectrum). Let `U` be
`d × m` with orthonormal columns, `m ≥ 6`, and `D_U` of full column rank with singular values
`a_j`. At most `2m` of them exceed `1/2`, and there is an index set `I` with
`ℓ = |I| ≥ t − 2m ≥ m²/4` and `a_j ≤ 1/2` on `I` (84). For every such `I` and every choice of
orthonormal right and left singular vectors `B_j ∈ Sym_m`, `y_j ∈ ℝ^d` (`j ∈ I`):
`y_j` is an eigenvector of `D_rest D_rest*` with eigenvalue `1 − a_j²`; the rest block
`r_j = −(a_j/(1 − a_j²)) D_rest* y_j` is the minimum-norm rest block with
`D_rest(r_j) = −a_j y_j` and `‖r_j‖_F² = a_j²/(1 − a_j²)` (85); the matrices
`Q_j = U B_j Uᵀ + r_j` are zero-diagonal, mutually Frobenius-orthogonal, with
`‖Q_j‖_F² = (1 − a_j²)⁻¹ ∈ [1, 4/3]` (86), and the `r_j` are mutually orthogonal; and
`(1/ℓ) Σ_I a_j^{-2} ≥ ((1/ℓ) Σ_I a_j)^{-2}`, `Σ_I a_j ≤ Σ_j a_j ≤ m`,
`Σ_I a_j^{-2} ≥ ℓ³/(Σ_I a_j)² ≥ ℓ³/m² ≳ m⁴` (87), with a universal constant. -/
theorem eq_84_87 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d m : ℕ) (U : Matrix (Fin d) (Fin m) ℝ), 10 ≤ d → Uᵀ * U = 1 → 6 ≤ m →
        FullColRank U →
        ((Finset.univ.filter (fun j => (1 / 2 : ℝ) < singVals U j)).card ≤ 2 * m) ∧
        (∃ I : Finset (SymIdx m),
          (Fintype.card (SymIdx m) : ℝ) - 2 * m ≤ (I.card : ℝ) ∧
          (m : ℝ) ^ 2 / 4 ≤ (Fintype.card (SymIdx m) : ℝ) - 2 * m ∧
          ∀ j ∈ I, singVals U j ≤ 1 / 2) ∧
        (∀ (I : Finset (SymIdx m)),
          (Fintype.card (SymIdx m) : ℝ) - 2 * m ≤ (I.card : ℝ) →
          (∀ j ∈ I, singVals U j ≤ 1 / 2) →
          ∀ (B : SymIdx m → Matrix (Fin m) (Fin m) ℝ) (y : SymIdx m → Fin d → ℝ),
            (∀ j ∈ I, (B j).IsSymm) →
            (∀ i ∈ I, ∀ j ∈ I, frobInner (B i) (B j) = if i = j then 1 else 0) →
            (∀ i ∈ I, ∀ j ∈ I, y i ⬝ᵥ y j = if i = j then 1 else 0) →
            (∀ j ∈ I, DU U (B j) = singVals U j • y j ∧ DUadj U (y j) = singVals U j • B j) →
            (∀ j ∈ I, diagVec (DrestAdj U (y j)) = (1 - singVals U j ^ 2) • y j) ∧
            (∀ j ∈ I,
              InRest U ((-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) ∧
              diagVec ((-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) =
                (-(singVals U j)) • y j ∧
              (∀ r' : Matrix (Fin d) (Fin d) ℝ, InRest U r' →
                diagVec r' = (-(singVals U j)) • y j →
                frobNorm ((-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) ≤
                  frobNorm r') ∧
              frobNorm ((-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) ^ 2 =
                singVals U j ^ 2 / (1 - singVals U j ^ 2)) ∧
            (∀ j ∈ I,
              IsSymZeroDiag (U * B j * Uᵀ +
                (-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) ∧
              frobNorm (U * B j * Uᵀ +
                (-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) ^ 2 =
                (1 - singVals U j ^ 2)⁻¹ ∧
              1 ≤ (1 - singVals U j ^ 2)⁻¹ ∧ (1 - singVals U j ^ 2)⁻¹ ≤ 4 / 3) ∧
            (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
              frobInner
                  (U * B i * Uᵀ + (-(singVals U i / (1 - singVals U i ^ 2))) • DrestAdj U (y i))
                  (U * B j * Uᵀ + (-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j))
                = 0 ∧
              frobInner ((-(singVals U i / (1 - singVals U i ^ 2))) • DrestAdj U (y i))
                  ((-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) = 0) ∧
            ((1 / (I.card : ℝ)) * ∑ j ∈ I, singVals U j)⁻¹ ^ 2 ≤
              (1 / (I.card : ℝ)) * ∑ j ∈ I, (singVals U j)⁻¹ ^ 2 ∧
            ∑ j ∈ I, singVals U j ≤ ∑ j, singVals U j ∧
            ∑ j, singVals U j ≤ (m : ℝ) ∧
            (I.card : ℝ) ^ 3 / (∑ j ∈ I, singVals U j) ^ 2 ≤ ∑ j ∈ I, (singVals U j)⁻¹ ^ 2 ∧
            (I.card : ℝ) ^ 3 / (m : ℝ) ^ 2 ≤ (I.card : ℝ) ^ 3 / (∑ j ∈ I, singVals U j) ^ 2 ∧
            c * (m : ℝ) ^ 4 ≤ (I.card : ℝ) ^ 3 / (m : ℝ) ^ 2) := by sorry

end HigherOrderId.Certify
