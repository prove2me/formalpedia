-- Prove2me | Theorems.Thm_OAI_Saxl_young_orbit_map
-- name    : OAI.Saxl.young_orbit_map
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:42:33.220273+00:00
-- url     : https://prove2.me/theorems/24ff817a-680c-43ff-be8c-f6d632829290
-- title:
--   Young's rule as an equivariant map from the word space to a dominating Specht module that is nonzero on a given word
-- statement:
--   Throughout, $[n]=\{0,1,\dots,n-1\}$ and $S_n$ is the symmetric group on $[n]$. For $n,d\in\mathbb{N}$ let $W_{n,d}$ be the space of complex-valued functions on words $w:[n]\to[d]$, with basis vectors $e_w$ (the indicator function of $w$); $S_n$ acts by permuting positions, $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot e_w=e_{w\circ g^{-1}}$. Thus $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$ with $S_n$ permuting the tensor factors. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) that is closed under moving up or to the left; $\mu_i$ is the length of row $i$, $|\mu|$ the number of cells and $\ell(\mu)$ the number of nonempty rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$ (so $n=|\mu|$). Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of the cell $t(i)$, and its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$. The polytabloid of $t$ is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot e_{r_t}\in W_{n,\ell(\mu)}$, and the Specht module $S^t=\operatorname{span}_{\mathbb{C}}\{g\cdot e_t:g\in S_n\}\subseteq W_{n,\ell(\mu)}$ is a representation of $S_n$ under the restricted action.
--
--   For a Young diagram $\lambda$ and $q\in\mathbb{N}$ write $P_q(\lambda)=\sum_{i<q}\lambda_i$ for the number of cells in the first $q$ rows. A diagram $\tau$ dominates $\theta$, written $\tau\trianglerighteq\theta$, if $P_q(\theta)\le P_q(\tau)$ for every $q\in\mathbb{N}$.
--
--   Let $\theta$ and $\tau$ be Young diagrams with $|\tau|=|\theta|$ and $\tau\trianglerighteq\theta$, and let $t$ be a tableau of shape $\tau$ on $n$ positions. Let $w:[n]\to[\ell(\theta)]$ be a word and $\pi$ a permutation of the alphabet $[\ell(\theta)]$ such that the letter $\pi(j)$ occurs in $w$ exactly $\theta_j$ times, for every $j\in[\ell(\theta)]$. Then there is an $S_n$-equivariant linear map from the word space to the Specht module of $t$ that does not vanish on $e_w$:
--
--   $$
--   \exists\,F\in\operatorname{Hom}_{S_n}\bigl(W_{n,\ell(\theta)},\,S^t\bigr)\qquad\text{with}\qquad F(e_w)\neq0.
--   $$
--
--   Restricted to the cyclic module $\mathbb{C}[S_n]e_w$, the span of all words with the same letter multiplicities as $w$ and hence a copy of the permutation module $M^\theta$ induced from the trivial representation of a Young subgroup of type $\theta$, the map $F$ is a nonzero equivariant map to $S^t$. This is Young's rule in the concrete form of an orbit map out of a single basis word, with the content of $w$ allowed to be any rearrangement of the row lengths of $\theta$ among the letters.
--
--   **Formalization Note** $\ell(\theta)$ is `θ.colLen 0` and $\theta_j$ is `θ.rowLen j`; $\pi$ is `e : Equiv.Perm (Fin (θ.colLen 0))` and $e_w$ is `Pi.single w 1`. The hypotheses force $n=|\tau|$. `Dominates τ θ` is the prefix-sum condition alone.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/CyclicTensor.lean#L20-L70

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

open OAI OAI.Saxl
open scoped TensorProduct
universe uG uX uY

theorem OAI.Saxl.young_orbit_map {n : ℕ} (θ τ : YoungDiagram) (t : Tableau n τ)
    (hc : τ.card = θ.card) (hd : Dominates τ θ)
    (w : Fin n → Fin (θ.colLen 0)) (e : Equiv.Perm (Fin (θ.colLen 0)))
    (hw : ∀ j, (Finset.univ.filter (fun i => w i = e j)).card = θ.rowLen j) :
    ∃ F : Representation.IntertwiningMap (wordRep n (θ.colLen 0)) (spechtRep t),
      F (Pi.single w 1) ≠ 0 := by sorry
