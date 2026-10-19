-- Prove2me | Theorems.Thm_OAI_Saxl_staircase_sign_equiv
-- name    : OAI.Saxl.staircase_sign_equiv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:46:37.243857+00:00
-- url     : https://prove2.me/theorems/6f12c55e-24ae-4b11-ae1c-f882ba1f5960
-- title:
--   The staircase Specht module is the sign twist of the Specht module of the transposed tableau
-- statement:
--   Throughout, $[n]=\{0,1,\dots,n-1\}$ and $S_n$ is the symmetric group on $[n]$. For $n,d\in\mathbb{N}$ let $W_{n,d}$ be the space of complex-valued functions on words $w:[n]\to[d]$, with basis vectors $e_w$ (the indicator function of $w$); $S_n$ acts by permuting positions, $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot e_w=e_{w\circ g^{-1}}$. Thus $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$ with $S_n$ permuting the tensor factors. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) that is closed under moving up or to the left; $\mu_i$ is the length of row $i$, $|\mu|$ the number of cells and $\ell(\mu)$ the number of nonempty rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$ (so $n=|\mu|$). Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of the cell $t(i)$, and its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$. The polytabloid of $t$ is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot e_{r_t}\in W_{n,\ell(\mu)}$, and the Specht module $S^t=\operatorname{span}_{\mathbb{C}}\{g\cdot e_t:g\in S_n\}\subseteq W_{n,\ell(\mu)}$ is a representation of $S_n$ under the restricted action.
--
--   For $m\in\mathbb{N}$ let $\delta_m=\{(i,j)\in\mathbb{N}^2:i+j<m\}$ be the staircase diagram, with $N=|\delta_m|=m(m+1)/2$ cells and $\ell(\delta_m)=m$ rows, and let $T$ be a fixed reference tableau of shape $\delta_m$ on $N$ positions. Transposition $(i,j)\mapsto(j,i)$ maps $\delta_m$ onto itself, and $T'$ denotes the tableau obtained by following $T$ with this transposition, so the row of $T'(i)$ is the column of $T(i)$ and vice versa. For a representation $\rho$ of $S_N$ on a space $V$, the sign twist $\operatorname{sgn}\otimes\rho$ is the representation $g\mapsto\operatorname{sgn}(g)\,\rho(g)$ on the same space $V$. The theorem states that for every $m\in\mathbb{N}$ there is an isomorphism of $S_N$-representations
--
--   $$
--   S^{T}\ \cong\ \operatorname{sgn}\otimes S^{T'} .
--   $$
--
--   This is the classical relation $S^{\lambda'}\cong\operatorname{sgn}\otimes S^{\lambda}$ for the self-conjugate staircase $\lambda=\lambda'=\delta_m$, realized with explicit tableaux, so that the column group of $T'$ is the row group of $T$. Such an isomorphism allows one to replace one factor of the tensor square of the staircase Specht module by its sign twist.
--
--   **Formalization Note** $T$ is `stairTableau m` (the canonical enumeration of the cells of `staircase m`), $T'$ is `stairRowTableau m`, and the sign twist is `signTwist`. The conclusion is `Nonempty` of a `Representation.Equiv`, i.e. the existence of an equivariant linear isomorphism.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/StaircaseSign.lean#L97-L157

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseSign

open OAI OAI.Saxl
open scoped TensorProduct
universe uX uY uZ

theorem OAI.Saxl.staircase_sign_equiv (m : ℕ) :
    Nonempty ((spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) := by sorry
