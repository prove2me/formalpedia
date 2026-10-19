-- Prove2me | Theorems.Thm_OAI_Saxl_repeatedTarget_in_quotient
-- name    : OAI.Saxl.repeatedTarget_in_quotient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:48:15.88635+00:00
-- url     : https://prove2.me/theorems/11caa513-4a7d-433a-95c1-2f6eeca54d82
-- title:
--   The indicator of the reversed staircase row word lies in the image of the sign-twisted pair-sum map on the staircase cyclic module
-- statement:
--   Throughout, $[d]=\{0,1,\dots,d-1\}$. For $n,d\in\mathbb{N}$ let $M_{n,d}$ be the complex vector space of functions on words $w:[n]\to[d]$ (positions $[n]$, letters $[d]$), with basis vectors $\delta_w$ and with the symmetric group $\mathfrak S_n$ acting by $(g\cdot f)(w)=f(w\circ g)$, so that $g\cdot\delta_w=\delta_{w\circ g^{-1}}$. Identifying a letter of $[d^2]$ with a pair of letters in $[d]\times[d]$, a word $w$ over $[d^2]$ is a pair $(w^{(1)},w^{(2)})$ of words over $[d]$, and $(x\boxtimes y)(w)=x(w^{(1)})\,y(w^{(2)})$ defines an $\mathfrak S_n$-equivariant isomorphism $M_{n,d}\otimes M_{n,d}\cong M_{n,d^2}$ (diagonal action on the tensor product).
--
--   A Young diagram $\lambda$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$) closed under moving up or to the left; $\lambda_i$ is the length of row $i$ (zero for empty rows) and $\ell(\lambda)$ the number of nonempty rows. A tableau of shape $\lambda$ with $|\lambda|=n$ is any bijection $t:[n]\to\lambda$ from positions to cells. Its row word $r_t:[n]\to[\ell(\lambda)]$ sends $p$ to the row of $t(p)$; its column group $C_t\le\mathfrak S_n$ consists of the permutations $g$ such that $t(g(p))$ and $t(p)$ lie in the same column for every $p$; its polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\delta_{r_t}\in M_{n,\ell(\lambda)}$; and the Specht module $S^t\subseteq M_{n,\ell(\lambda)}$ is the span of the vectors $g\cdot e_t$, $g\in\mathfrak S_n$.
--
--   The staircase of size $m$ is $\delta_m=\{(i,j)\in\mathbb{N}^2: i+j<m\}$; its row $i$ has $m-i$ cells for $i<m$, it has $m$ rows, and $|\delta_m|=m(m+1)/2$. Let $t_m$ be a fixed (canonical) tableau of $\delta_m$, and let $t_m^{*}$ be its transpose, $t_m^*(p)=(j,i)$ whenever $t_m(p)=(i,j)$; this is again a tableau of $\delta_m$ because $\delta_m$ is self-conjugate, and its column group $C_{t_m^*}$ is the group of permutations preserving the rows of $t_m$. The staircase vector and the staircase cyclic module are
--
--   $$\Omega_m=e_{t_m^*}\boxtimes e_{t_m}\in M_{n,m^2},\qquad C_m=\operatorname{span}\{g\cdot\Omega_m: g\in\mathfrak S_n\}\subseteq M_{n,m^2},\qquad n=|\delta_m|.$$
--
--   For a representation $V$ of $\mathfrak S_n$, $\operatorname{sgn}\otimes V$ denotes the same space with $g$ acting by $\operatorname{sgn}(g)\,g$. Let $\varphi:S^{t_m}\to\operatorname{sgn}\otimes S^{t_m^*}$ be any isomorphism of $\mathfrak S_n$-representations, and build the following maps.
--
--   1. $A_\varphi=\iota\circ\varphi\circ P:M_{n,m}\to M_{n,m}$, where $P$ is the orthogonal projection of $M_{n,m}$ onto $S^{t_m}$ (for the inner product in which the $\delta_w$ are orthonormal) and $\iota$ is the inclusion $S^{t_m^*}\subseteq M_{n,m}$. It satisfies $A_\varphi(g\cdot x)=\operatorname{sgn}(g)\,g\cdot A_\varphi(x)$.
--   2. The letterwise sum $\Sigma:M_{n,m^2}\to M_{n,m}$, $\Sigma(\delta_{(a,b)})=\delta_{a+b}$ if $a(p)+b(p)\le m-1$ for all positions $p$, and $\Sigma(\delta_{(a,b)})=0$ otherwise.
--   3. For a word $T$ over $[m]$, the coordinate projection $\pi_T$ of $M_{n,m}$ onto the span of the $\delta_w$ with $w=T\circ g$ a rearrangement of $T$.
--   4. The target word $T_m:[n]\to[m]$, $T_m(p)=m-1-r_{t_m}(p)$.
--
--   The dominated quotient map is the $\mathfrak S_n$-equivariant linear map $Q_\varphi:\operatorname{sgn}\otimes C_m\to M_{n,m}$, $Q_\varphi(z)=\pi_{T_m}\big(\Sigma((\mathrm{id}\boxtimes A_\varphi)(z))\big)$, where $(\mathrm{id}\boxtimes A_\varphi)(x\boxtimes y)=x\boxtimes A_\varphi(y)$. The theorem states that for every $m\in\mathbb{N}$ and every such isomorphism $\varphi$,
--
--   $$\delta_{T_m}\in Q_\varphi(C_m).$$
--
--   In the word $T_m$ the letter $m-1-i$ occurs exactly $m-i$ times, so the span of the rearrangements of $T_m$ is a copy of the permutation module of the staircase shape. Since $Q_\varphi$ is equivariant and its image lies in that span, the theorem says equivalently that $Q_\varphi$ maps $\operatorname{sgn}\otimes C_m$ onto this permutation module. Combined with Young's rule, this makes every Specht module whose shape dominates the staircase a quotient of $\operatorname{sgn}\otimes C_m$. After untwisting by the sign, every Specht module whose shape is dominated by the staircase is then a quotient of $C_m$. This is how the dominated case of the staircase tensor-square argument is obtained.
--
--   **Formalization Note** The map $Q_\varphi$ is `dominatedQuotient m φ`, the word $T_m$ is `repeatedTarget m`, $C_m$ is `staircaseCyclic m`, $t_m$ is `stairTableau m` and $t_m^*$ is `stairRowTableau m`; the alphabet size $m$ appears as `(staircase m).colLen 0`. The projection $P$ is `subrepProject`, defined through the bilinear coordinate pairing; it coincides with the orthogonal projection because $S^{t_m}$ is closed under complex conjugation. No hypothesis on $m$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/DominatedQuotient.lean#L93-L119

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
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedQuotient

open OAI OAI.Saxl
open scoped TensorProduct

theorem OAI.Saxl.repeatedTarget_in_quotient (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Pi.single (repeatedTarget m) (1:ℂ) ∈ (dominatedQuotient m φ).range := by sorry
