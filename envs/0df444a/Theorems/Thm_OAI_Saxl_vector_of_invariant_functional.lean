-- Prove2me | Theorems.Thm_OAI_Saxl_vector_of_invariant_functional
-- name    : OAI.Saxl.vector_of_invariant_functional
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:40:53.049487+00:00
-- url     : https://prove2.me/theorems/3cc53f01-12bb-448d-9810-c15efd81ca02
-- title:
--   An invariant linear functional on a Specht module yields an invariant vector
-- statement:
--   Throughout, $[n]=\{0,1,\dots,n-1\}$ and $S_n$ is the symmetric group on $[n]$. For $n,d\in\mathbb{N}$ let $W_{n,d}$ be the space of complex-valued functions on words $w:[n]\to[d]$, with basis vectors $e_w$ (the indicator function of $w$); $S_n$ acts by permuting positions, $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot e_w=e_{w\circ g^{-1}}$. Thus $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$ with $S_n$ permuting the tensor factors. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) that is closed under moving up or to the left; $\mu_i$ is the length of row $i$, $|\mu|$ the number of cells and $\ell(\mu)$ the number of nonempty rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$ (so $n=|\mu|$). Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of the cell $t(i)$, and its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$. The polytabloid of $t$ is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot e_{r_t}\in W_{n,\ell(\mu)}$, and the Specht module $S^t=\operatorname{span}_{\mathbb{C}}\{g\cdot e_t:g\in S_n\}\subseteq W_{n,\ell(\mu)}$ is a representation of $S_n$ under the restricted action.
--
--   Let $t$ be a tableau of shape $\mu$ on $n$ positions, let $a:[n]\to[d]$ be an arbitrary word (a colouring of the positions), and let $\operatorname{Stab}(a)=\{g\in S_n:a\circ g=a\}$ be its stabilizer, the Young subgroup permuting positions of equal colour. Let $\lambda:S^t\to\mathbb{C}$ be a nonzero linear functional with $\lambda(g\cdot x)=\lambda(x)$ for all $g\in\operatorname{Stab}(a)$ and $x\in S^t$. Then $S^t$ contains a nonzero vector fixed by the same subgroup:
--
--   $$
--   \exists\,y\in S^t,\ y\neq0,\qquad g\cdot y=y\quad\text{for all }g\in S_n\text{ with }a\circ g=a.
--   $$
--
--   In other words, $\operatorname{Hom}_{\operatorname{Stab}(a)}(S^t,\mathbb{C})\neq0$ implies that the space of $\operatorname{Stab}(a)$-invariant vectors of $S^t$ is nonzero. This reflects the self-duality of complex Specht modules; it converts the invariant functionals produced by Young's rule into invariant vectors, from which equivariant maps out of permutation modules are built.
--
--   **Formalization Note** The functional is an element of `Module.Dual ℂ (Specht t)`. The invariant vector comes from the equivariant isomorphism `spechtSelfDual t` between the Specht representation and its contragredient.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/YoungRule.lean#L92-L112

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

theorem OAI.Saxl.vector_of_invariant_functional {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin d) (l : Module.Dual ℂ (Specht t)) (hl : l ≠ 0)
    (he : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ∀ x, l (spechtRep t g x) = l x) :
    ∃ y : Specht t, y ≠ 0 ∧ ∀ g : Equiv.Perm (Fin n), a ∘ g = a → spechtRep t g y = y := by sorry
