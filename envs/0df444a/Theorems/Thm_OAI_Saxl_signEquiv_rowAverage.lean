-- Prove2me | Theorems.Thm_OAI_Saxl_signEquiv_rowAverage
-- name    : OAI.Saxl.signEquiv_rowAverage
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:47:14.68686+00:00
-- url     : https://prove2.me/theorems/c0cb3796-9f43-4b42-8c88-39d2e81db927
-- title:
--   A sign-twisted staircase isomorphism maps the row-symmetrized polytabloid to a nonzero multiple of the transposed polytabloid
-- statement:
--   Throughout, $[n]=\{0,1,\dots,n-1\}$ and $S_n$ is the symmetric group on $[n]$. For $n,d\in\mathbb{N}$ let $W_{n,d}$ be the space of complex-valued functions on words $w:[n]\to[d]$, with basis vectors $e_w$ (the indicator function of $w$); $S_n$ acts by permuting positions, $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot e_w=e_{w\circ g^{-1}}$. Thus $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$ with $S_n$ permuting the tensor factors. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) that is closed under moving up or to the left; $\mu_i$ is the length of row $i$, $|\mu|$ the number of cells and $\ell(\mu)$ the number of nonempty rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$ (so $n=|\mu|$). Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of the cell $t(i)$, and its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$. The polytabloid of $t$ is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot e_{r_t}\in W_{n,\ell(\mu)}$, and the Specht module $S^t=\operatorname{span}_{\mathbb{C}}\{g\cdot e_t:g\in S_n\}\subseteq W_{n,\ell(\mu)}$ is a representation of $S_n$ under the restricted action.
--
--   For $m\in\mathbb{N}$ let $\delta_m=\{(i,j)\in\mathbb{N}^2:i+j<m\}$ be the staircase diagram, with $N=|\delta_m|=m(m+1)/2$ cells and $\ell(\delta_m)=m$ rows, and let $T$ be a fixed reference tableau of shape $\delta_m$ on $N$ positions. Transposition $(i,j)\mapsto(j,i)$ maps $\delta_m$ onto itself, and $T'$ denotes the tableau obtained by following $T$ with this transposition, so the row of $T'(i)$ is the column of $T(i)$ and vice versa. For a representation $\rho$ of $S_N$ on a space $V$, the sign twist $\operatorname{sgn}\otimes\rho$ is the representation $g\mapsto\operatorname{sgn}(g)\,\rho(g)$ on the same space $V$. Let $R_T=C_{T'}$ be the group of permutations preserving every row of $T$ (equivalently every column of $T'$), and let $\rho_m=\sum_{g\in R_T}g\cdot e_T\in S^T$ be the row symmetrization of the staircase polytabloid.
--
--   The theorem states that for every $m\in\mathbb{N}$ and every isomorphism $\varphi:S^T\to\operatorname{sgn}\otimes S^{T'}$ of $S_N$-representations there is a scalar $c\in\mathbb{C}$ with
--
--   $$
--   \varphi(\rho_m)=c\,e_{T'},\qquad c\neq0 .
--   $$
--
--   Thus every such isomorphism (one exists by the sign-twist theorem for the staircase) is pinned down on the row-symmetrized polytabloid: it sends it to a nonzero multiple of the polytabloid of the transposed tableau. This normalization makes the sign twist computable on concrete vectors of the staircase Specht module.
--
--   **Formalization Note** $\rho_m$ is `rowAverage m`, defined as a sum over the column group of `stairRowTableau m`; the identity is between the underlying vectors in the word space, with $e_{T'}$ = `polytabloid (stairRowTableau m)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/StaircaseSign.lean#L212-L229

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

theorem OAI.Saxl.signEquiv_rowAverage (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    ∃ c : ℂ, c ≠ 0 ∧ (φ (rowAverage m)).val = c • polytabloid (stairRowTableau m) := by sorry
