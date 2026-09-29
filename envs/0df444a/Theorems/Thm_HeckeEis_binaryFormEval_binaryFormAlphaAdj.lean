-- Prove2me | Theorems.Thm_HeckeEis_binaryFormEval_binaryFormAlphaAdj
-- name    : HeckeEis.binaryFormEval_binaryFormAlphaAdj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/659c297d-1dac-5ed0-ae2b-da1f2fb06262
-- title:
--   Evaluation map intertwines diag(ℓ,1) on forms and on P¹(ℤ/p)
-- statement:
--   Let $p$ be a prime, let $K$ be a commutative ring of characteristic $p$, and let $\ell$ be a natural number coprime to $p$ (the hypothesis is `p.Coprime ℓ`). Two $K$-linear maps are compared on the submodule [`HeckeEis.BinaryForm K (p - 1)`](def/HeckeEis_BinaryFormRep.html#L25) of polynomials in $K[X_0,X_1]$ that are homogeneous of degree $p-1$. The first is [`HeckeEis.binaryFormAlphaAdj K (p - 1) ℓ`](def/HeckeEis_BinaryFormRep.html#L82), the restriction to that submodule of the $K$-algebra endomorphism of $K[X_0,X_1]$ substituting $X_j \mapsto \sum_i (M_{ij} \bmod p)X_i$ for $M = \begin{pmatrix}\ell&0\\0&1\end{pmatrix}$ over $\mathbb{Z}$, that is $F \mapsto F(\ell X_0, X_1)$. The second is [`HeckeEis.binaryFormEval p K`](def/HeckeEis_BinaryFormRep.html#L114), which sends a homogeneous $F$ of degree $p-1$ to the function on $\mathbb{P}^1(\mathbb{Z}/p)$ — the quotient of the unimodular rows over $\mathbb{Z}/p$ by unit scaling — whose value on the class of a row $v=(v_1,v_2)$ is $F$ evaluated at the images of $v_1,v_2$ under the ring map $\mathbb{Z}/p \to K$. Finally, [`HeckeEis.projLineAlphaAdj p K ℓ`](def/ProjectiveLineMatrixAction.html#L152) is precomposition of functions $\mathbb{P}^1(\mathbb{Z}/p) \to K$ with the map [`HeckeEis.projLineAct p`](def/ProjectiveLineMatrixAction.html#L74) attached to the same matrix, namely right multiplication of rows by its reduction mod $p$ when that reduction has unit determinant and the identity otherwise. The assertion is that evaluating $F(\ell X_0, X_1)$ equals the evaluation of $F$ transported along the action of $\mathrm{diag}(\ell,1)$ on $\mathbb{P}^1(\mathbb{Z}/p)$, i.e. `binaryFormEval p K` composed after `binaryFormAlphaAdj K (p - 1) ℓ` equals `projLineAlphaAdj p K ℓ` composed after `binaryFormEval p K`.
--
--   This is the compatibility of the evaluation map $\mathrm{Sym}^{p-1} \to K[\mathbb{P}^1(\mathbb{Z}/p)]$ with the coefficient parts of the Hecke operator $T_\ell$ on the two coefficient modules, $\mathrm{diag}(\ell,1)$ being the adjugate of $\mathrm{diag}(1,\ell)$. It is used in [`HeckeEis.exists_retraction_binaryFormEval`](thm.html#HeckeEis.exists_retraction_binaryFormEval) and in [`WeierstrassCurve.exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two_or_succ`](thm.html#WeierstrassCurve.exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two_or_succ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_binaryFormEval_binaryFormAlphaAdj.lean

import Mathlib
import Definitions.Def_ProjectiveLineMatrixAction
import Definitions.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.binaryFormEval_binaryFormAlphaAdj (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p] (ℓ : ℕ) (hℓ : p.Coprime ℓ) :
    HeckeEis.binaryFormEval p K ∘ₗ HeckeEis.binaryFormAlphaAdj K (p - 1) ℓ
      = HeckeEis.projLineAlphaAdj p K ℓ ∘ₗ HeckeEis.binaryFormEval p K := by sorry
