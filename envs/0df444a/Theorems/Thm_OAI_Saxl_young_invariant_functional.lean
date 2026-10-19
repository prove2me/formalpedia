-- Prove2me | Theorems.Thm_OAI_Saxl_young_invariant_functional
-- name    : OAI.Saxl.young_invariant_functional
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:41:34.883316+00:00
-- url     : https://prove2.me/theorems/45691b67-8523-4f79-b878-dd6aa687ab5b
-- title:
--   Young's rule, sufficiency: a dominating Specht module has a nonzero Young-subgroup-invariant functional
-- statement:
--   Throughout, $[n]=\{0,1,\dots,n-1\}$ and $S_n$ is the symmetric group on $[n]$. For $n,d\in\mathbb{N}$ let $W_{n,d}$ be the space of complex-valued functions on words $w:[n]\to[d]$, with basis vectors $e_w$ (the indicator function of $w$); $S_n$ acts by permuting positions, $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot e_w=e_{w\circ g^{-1}}$. Thus $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$ with $S_n$ permuting the tensor factors. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) that is closed under moving up or to the left; $\mu_i$ is the length of row $i$, $|\mu|$ the number of cells and $\ell(\mu)$ the number of nonempty rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$ (so $n=|\mu|$). Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of the cell $t(i)$, and its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$. The polytabloid of $t$ is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot e_{r_t}\in W_{n,\ell(\mu)}$, and the Specht module $S^t=\operatorname{span}_{\mathbb{C}}\{g\cdot e_t:g\in S_n\}\subseteq W_{n,\ell(\mu)}$ is a representation of $S_n$ under the restricted action. For every Young diagram $\tau$ fix a reference tableau $T_\tau$ of shape $\tau$ on $|\tau|$ positions (a fixed enumeration of its cells).
--
--   For a Young diagram $\lambda$ and $q\in\mathbb{N}$ write $P_q(\lambda)=\sum_{i<q}\lambda_i$ for the number of cells in the first $q$ rows. A diagram $\tau$ dominates $\theta$, written $\tau\trianglerighteq\theta$, if $P_q(\theta)\le P_q(\tau)$ for every $q\in\mathbb{N}$.
--
--   Let $\theta$ and $\tau$ be Young diagrams with $|\tau|=|\theta|=N$ and $\tau\trianglerighteq\theta$. Then there exist a word $a:[N]\to[\ell(\theta)]$ of content $\theta$ and a nonzero linear functional $\lambda$ on $S^{T_\tau}$ that is invariant under the stabilizer of $a$:
--
--   $$
--   |a^{-1}(j)|=\theta_j\ \ \bigl(j\in[\ell(\theta)]\bigr),\qquad\lambda\neq0,\qquad\lambda(g\cdot x)=\lambda(x)\ \ \text{for all }x\in S^{T_\tau}\text{ and }g\in S_N\text{ with }a\circ g=a.
--   $$
--
--   The stabilizer of $a$ is a Young subgroup $S_\theta\cong S_{\theta_0}\times S_{\theta_1}\times\cdots$, so the theorem says that the restriction of the Specht module of $\tau$ to this Young subgroup has a nonzero invariant functional. By Frobenius reciprocity this means that the Specht module of $\tau$ is a constituent of the permutation module $M^\theta=\operatorname{Ind}_{S_\theta}^{S_N}\mathbb{C}$: this is the sufficiency half of Young's rule (the Kostka number $K_{\tau\theta}$ is positive whenever $\tau\trianglerighteq\theta$), in the form used to build equivariant maps from word spaces onto Specht modules.
--
--   **Formalization Note** $T_\tau$ is `shapeTableau τ`, the canonical enumeration of the cells by `Fin τ.card`; $\ell(\theta)$ is `θ.colLen 0` and $\theta_j$ is `θ.rowLen j`. `Dominates τ θ` is the prefix-sum condition alone, so equality of sizes is a separate hypothesis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/YoungRule.lean#L117-L173

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

open OAI OAI.Saxl
open scoped TensorProduct

theorem OAI.Saxl.young_invariant_functional (θ τ : YoungDiagram)
    (hc : τ.card = θ.card) (hd : Dominates τ θ) :
    ∃ (a : Fin τ.card → Fin (θ.colLen 0)) (l : Module.Dual ℂ (Specht (shapeTableau τ))),
      l ≠ 0 ∧
      (∀ j, (Finset.univ.filter (fun i => a i = j)).card = θ.rowLen j) ∧
      (∀ g : Equiv.Perm (Fin τ.card), a ∘ g = a →
        ∀ x, l (spechtRep (shapeTableau τ) g x) = l x) := by sorry
