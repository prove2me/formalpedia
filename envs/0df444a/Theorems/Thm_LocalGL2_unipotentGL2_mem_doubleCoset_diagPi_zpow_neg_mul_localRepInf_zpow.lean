-- Prove2me | Theorems.Thm_LocalGL2_unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow
-- name    : LocalGL2.unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/72d21699-6686-5199-88cf-62dc9f31bc87
-- title:
--   Unipotent matrices in Cartan double cosets over K
-- statement:
--   Let $R$ be a commutative ring, $K$ a field and $R \to K$ an algebra structure, and let $\varpi \in R$ be an element whose image $\varpi_K = \mathrm{algebraMap}\,\varpi$ in $K$ is nonzero. Write $U =$ [`LocalGL2.integralSubgroup R K`](def/LocalLanglands_LocalHeckeInstance.html#L13) for the image of $GL_2(R)$ in $GL_2(K)$ under the map induced by $R \to K$, $n(x) = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$ for [`AutomorphicForm.unipotentGL2`](def/AutomorphicForm_ConstantTerm.html#L17), $P =$ [`LocalGL2.diagPi`](def/LocalLanglands_HeckeCosetLocal.html#L68) $= \mathrm{diag}(\varpi_K, 1)$, and $Q =$ [`LocalGL2.localRepInf`](def/LocalLanglands_HeckeCosetLocal.html#L98) $= wPw$ with $w$ the image in $GL_2(K)$ of the Weyl matrix `weylR` over $R$, so that $Q = \mathrm{diag}(1,\varpi_K)$; for $g \in GL_2(K)$, [`HeckePair.doubleCoset U g`](def/LocalLanglands_HeckePair.html#L405) is the set $U \cdot \{g\} \cdot U$. The theorem asserts two things. First, for every $b \in R$ the matrix $n(b_K)$ lies in $U\,P^{0}Q^{0}\,U = U$, the integer exponents being written as $0 : \mathbb{Z}$. Second, for every unit $u \in R^{\times}$ and every natural number $r$, the matrix $n(u_K\,\varpi_K^{-r})$ lies in the double coset $U\,P^{-r}Q^{\,r}\,U$, with exponents $-(r:\mathbb{Z})$ and $(r:\mathbb{Z})$. No discrete-valuation or fraction-field hypothesis on $R$ and $K$ is assumed.
--
--   This is the Cartan (elementary-divisor) position of an upper unipotent matrix: an integral unipotent matrix is itself integral, while $n(u\varpi^{-r})$ sits in the double coset of $\mathrm{diag}(\varpi^{-r},\varpi^{r})$, i.e. at distance $2r$ from the base vertex in the Bruhat–Tits tree picture. It is used in [`LocalGL2.sum_indicator_word_inv_mul_scalar_mul_unipotentGL2_mem_localIntegralSet_eq_walkCount`](thm.html#LocalGL2.sum_indicator_word_inv_mul_scalar_mul_unipotentGL2_mem_localIntegralSet_eq_walkCount), where counts of Hecke words are matched with walk counts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LocalGL2.unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow
    {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) :
    (∀ b : R, AutomorphicForm.unipotentGL2 (algebraMap R K b) ∈
        HeckePair.doubleCoset (LocalGL2.integralSubgroup R K)
          (LocalGL2.diagPi ϖ hϖ0 ^ (0 : ℤ) * LocalGL2.localRepInf ϖ hϖ0 ^ (0 : ℤ))) ∧
    ∀ (u : Rˣ) (r : ℕ),
      AutomorphicForm.unipotentGL2 (algebraMap R K u * ((algebraMap R K ϖ)⁻¹) ^ r) ∈
        HeckePair.doubleCoset (LocalGL2.integralSubgroup R K)
          (LocalGL2.diagPi ϖ hϖ0 ^ (-(r : ℤ)) * LocalGL2.localRepInf ϖ hϖ0 ^ (r : ℤ)) := by sorry
