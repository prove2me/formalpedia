-- Prove2me | Theorems.Thm_OAI_Saxl_specht_sign_transpose
-- name    : OAI.Saxl.specht_sign_transpose
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:23:50.079463+00:00
-- url     : https://prove2.me/theorems/d0f9aa09-1e5f-40cc-99fd-3081a28e2615
-- title:
--   Specht modules of transposed tableaux differ by the sign character
-- statement:
--   Write $[m]=\{0,1,\dots,m-1\}$ and let $S_m$ be the symmetric group on $[m]$. For $m,d\in\mathbb{N}$ let $W_{m,d}$ be the space of functions from words $w:[m]\to[d]$ to $\mathbb{C}$, on which $S_m$ acts by $(g\cdot x)(w)=x(w\circ g)$; thus the indicator $\delta_w$ of a word is sent to $\delta_{w\circ g^{-1}}$. A Young diagram $\lambda$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ ($i$ the row, $j$ the column) that is closed under moving up or to the left; $|\lambda|$ is its number of cells and $\ell(\lambda)$ its number of rows. A tableau of shape $\lambda$ on $[m]$ is a bijection $t:[m]\to\lambda$ (so $|\lambda|=m$). Its row word $r_t:[m]\to[\ell(\lambda)]$ sends $k$ to the row of $t(k)$; its column group $C_t\le S_m$ consists of the permutations $g$ such that $t(g(k))$ and $t(k)$ lie in the same column for every $k$; its polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\delta_{r_t}\in W_{m,\ell(\lambda)}$; and its Specht module $S^t\subseteq W_{m,\ell(\lambda)}$ is the $S_m$-invariant subspace spanned by $\{g\cdot e_t: g\in S_m\}$, with the restricted action.
--
--   The transpose $\mu'$ of a Young diagram $\mu$ has the cells $(j,i)$ for $(i,j)\in\mu$, and the transpose of a tableau $t:[n]\to\mu$ is the tableau $t':[n]\to\mu'$ with $t'(k)=(j,i)$ whenever $t(k)=(i,j)$. For a representation $\sigma$ of $S_n$, $\operatorname{sgn}\otimes\sigma$ denotes the representation $g\mapsto\operatorname{sgn}(g)\,\sigma(g)$ on the same space.
--
--   For every $n\in\mathbb{N}$, every Young diagram $\mu$ and every tableau $t:[n]\to\mu$ there is an isomorphism of $S_n$-representations
--   $$
--   S^{t}\;\cong\;\operatorname{sgn}\otimes S^{t'},
--   $$
--   that is, a linear bijection $\Psi:S^t\to S^{t'}$ with $\Psi(g\cdot x)=\operatorname{sgn}(g)\,g\cdot\Psi(x)$ for all $g\in S_n$ and $x\in S^t$.
--
--   This is the classical relation between the Specht modules of conjugate shapes, proved here for the concrete polytabloid models inside word spaces. It allows representation-theoretic statements about a shape to be transferred to its transpose, and the project uses it whenever it passes between a Young diagram and its transpose.
--
--   **Formalization Note** The transposed tableau is `transposeTableau t`, the sign twist is `signTwist`, and the statement is `Nonempty ((spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t))))`, where `Representation.Equiv` is an isomorphism of representations. The number of rows $\ell(\mu)$ is `μ.colLen 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/SignEquivalence.lean#L91-L150

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

open OAI OAI.Saxl
open scoped TensorProduct
universe uV

theorem OAI.Saxl.specht_sign_transpose {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Nonempty ((spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) := by sorry
