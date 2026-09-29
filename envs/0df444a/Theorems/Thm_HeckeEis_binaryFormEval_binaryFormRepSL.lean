-- Prove2me | Theorems.Thm_HeckeEis_binaryFormEval_binaryFormRepSL
-- name    : HeckeEis.binaryFormEval_binaryFormRepSL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/784c6a95-f375-57b2-95b7-d445361ec6b8
-- title:
--   SL₂(ℤ)-equivariance of evaluation of binary forms on P¹(ℤ/p)
-- statement:
--   Let $p$ be a prime, let $K$ be a commutative ring of characteristic $p$, and let $g \in SL(2,\mathbb{Z})$. Two $K$-linear maps out of the submodule $\mathrm{BinaryForm}\,K\,(p-1)$ of homogeneous polynomials of degree $p-1$ in $K[X_0,X_1]$ (with $p-1$ natural subtraction) into the $K$-module of functions $\mathrm{ProjectiveLine}(\mathbb{Z}/p) \to K$, where $\mathrm{ProjectiveLine}(\mathbb{Z}/p)$ is the quotient of the unimodular rows over $\mathbb{Z}/p$ by unit scaling, are asserted to agree. The evaluation map [`HeckeEis.binaryFormEval p K`](def/HeckeEis_BinaryFormRep.html#L114) sends $F$ to the function whose value on the class of a unimodular row $v = (v_1,v_2)$ is the evaluation of $F$ at the images of $v_1,v_2$ under the canonical ring map $\mathbb{Z}/p \to K$; this is well defined because $F$ is homogeneous of degree $p-1$. The representation [`HeckeEis.binaryFormRepSL K (p-1)`](def/HeckeEis_BinaryFormRep.html#L61) acts at $g$ by the substitution $X_j \mapsto \sum_i (g_{ij} \bmod p \text{ in } K)\,X_i$ induced by the integer entries of $g$, restricted to homogeneous forms, and [`HeckeEis.projLineRepSL p K`](def/ProjectiveLineMatrixAction.html#L124) acts at $g$ by precomposition with `projLineAct`, i.e. with right multiplication by the reduction of $g$ modulo $p$ on unimodular rows when that reduction has unit determinant, and by the identity otherwise. The conclusion is that evaluation followed by the projective-line action of $g$ equals the binary-form action of $g$ followed by evaluation.
--
--   This is the equivariance half of the classical identification of $K[\mathbb{P}^1(\mathbb{F}_p)]$ with $\mathbf{1} \oplus \mathrm{Sym}^{p-1}$ as a representation of $SL_2(\mathbb{Z})$ in characteristic $p$, used in comparing weight $p+1$ at level $N$ with weight $2$ at level $Np$. It is cited in the construction of a retraction of the evaluation map and in the Hecke-algebra ideal comparison used for level raising at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_binaryFormEval_binaryFormRepSL.lean

import Mathlib
import Definitions.Def_ProjectiveLineMatrixAction
import Definitions.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.binaryFormEval_binaryFormRepSL (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p] (g : SL(2, ℤ)) :
    HeckeEis.binaryFormEval p K ∘ₗ HeckeEis.binaryFormRepSL K (p - 1) g
      = HeckeEis.projLineRepSL p K g ∘ₗ HeckeEis.binaryFormEval p K := by sorry
