-- Prove2me | Theorems.Thm_OAI_Saxl_placed_strip_restriction
-- name    : OAI.Saxl.placed_strip_restriction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:37:49.484239+00:00
-- url     : https://prove2.me/theorems/2ed538ec-a42c-4eea-85e0-41cfde11149f
-- title:
--   Iterated horizontal-strip restriction of a Specht module to an arbitrary block of positions
-- statement:
--   Throughout, $[n]=\{0,1,\dots,n-1\}$ and $S_n$ is the symmetric group on $[n]$. For $n,d\in\mathbb{N}$ let $W_{n,d}$ be the space of complex-valued functions on words $w:[n]\to[d]$, with basis vectors $e_w$ (the indicator function of $w$); $S_n$ acts by permuting positions, $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot e_w=e_{w\circ g^{-1}}$. Thus $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$ with $S_n$ permuting the tensor factors. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) that is closed under moving up or to the left; $\mu_i$ is the length of row $i$, $|\mu|$ the number of cells and $\ell(\mu)$ the number of nonempty rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$ (so $n=|\mu|$). Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of the cell $t(i)$, and its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$. The polytabloid of $t$ is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot e_{r_t}\in W_{n,\ell(\mu)}$, and the Specht module $S^t=\operatorname{span}_{\mathbb{C}}\{g\cdot e_t:g\in S_n\}\subseteq W_{n,\ell(\mu)}$ is a representation of $S_n$ under the restricted action.
--
--   A pair of Young diagrams $\eta\subseteq\mu$ is a horizontal strip if no two cells of $\mu\setminus\eta$ lie in the same column. For a list $\mathbf b=(b_0,\dots,b_{k-1})$ of natural numbers, a sized strip chain from $\nu$ to $\mu$ with sizes $\mathbf b$ is a chain of Young diagrams $\nu=\eta_0\subseteq\eta_1\subseteq\cdots\subseteq\eta_k=\mu$ such that every step $\eta_j\subseteq\eta_{j+1}$ is a horizontal strip with $|\eta_{j+1}|=|\eta_j|+b_j$.
--
--   Let $\varepsilon:[n]\to[a]\sqcup[b]$ be a bijection; it splits the positions into a left block $\varepsilon^{-1}([a])$ and a right block $\varepsilon^{-1}([b])$. For $h\in S_a$ and $q\in S_b$ let $h\oplus_\varepsilon q\in S_n$ be the permutation acting as $h$ on the left block and as $q$ on the right block, that is $(h\oplus_\varepsilon q)(\varepsilon^{-1}(\mathrm{inl}\,i))=\varepsilon^{-1}(\mathrm{inl}\,h(i))$ and $(h\oplus_\varepsilon q)(\varepsilon^{-1}(\mathrm{inr}\,j))=\varepsilon^{-1}(\mathrm{inr}\,q(j))$.
--
--   Let $\nu$ and $\mu$ be joined by a sized strip chain with sizes $\mathbf b$ of length $k$, let $s$ be a tableau of shape $\nu$ on $a$ positions, let $t$ be a tableau of shape $\mu$ on $n$ positions, and let $\varepsilon$ be an arbitrary bijection as above. Then there exist a colouring $c:[b]\to[k]$ of the right block and a surjective $\mathbb{C}$-linear map $F:S^t\to S^s$ such that
--
--   $$
--   F\bigl((h\oplus_\varepsilon q)\cdot x\bigr)=h\cdot F(x)\qquad\text{for all }h\in S_a,\ x\in S^t\text{ and all }q\in S_b\text{ with }c\circ q=c.
--   $$
--
--   Thus $S^s$ is an equivariant quotient of the restriction of $S^t$ to the subgroup $\{h\oplus_\varepsilon q: h\in S_a,\ c\circ q=c\}$, on which the colour-preserving permutations of the right block act trivially. This is an iterated positive Pieri rule in which the smaller tableau may occupy any prescribed set of $a$ positions; it is the restriction step that allows a constituent living on one block of positions to be combined with the strips carried by the complementary block.
--
--   **Formalization Note** The chain is the inductive predicate `SizedStripChain bs ν μ`, built by appending one horizontal strip of prescribed size at a time; $\varepsilon$ is `e : Fin n ≃ Fin a ⊕ Fin b` and $h\oplus_\varepsilon q$ is `sumPerm e h q`. The colouring takes values in `Fin bs.length`, and the statement does not record the sizes of its colour classes. Because $s$ and $t$ are bijections onto the cells, $a=|\nu|$ and $n=|\mu|=a+b$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/StripSupport.lean#L13-L68

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

open OAI OAI.Saxl
open scoped TensorProduct

theorem OAI.Saxl.placed_strip_restriction {n a b : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    ∃ (c : Fin b → Fin bs.length) (F : Specht t →ₗ[ℂ] Specht s), Function.Surjective F ∧
      ∀ (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)), c ∘ q = c →
        ∀ x, F (spechtRep t (sumPerm e h q) x) = spechtRep s h (F x) := by sorry
