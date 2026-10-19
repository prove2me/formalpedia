-- Prove2me | Theorems.Thm_OAI_Saxl_stripChain_restriction
-- name    : OAI.Saxl.stripChain_restriction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:34:31.545036+00:00
-- url     : https://prove2.me/theorems/aa8949e6-4b10-4fa3-bcce-0cbe1e028a78
-- title:
--   Iterated Pieri restriction along a chain of horizontal strips, with a coloring of the added strips
-- statement:
--   Write $[m]=\{0,1,\dots,m-1\}$ and let $S_m$ be the symmetric group on $[m]$. For $m,d\in\mathbb{N}$ let $W_{m,d}$ be the space of functions from words $w:[m]\to[d]$ to $\mathbb{C}$, on which $S_m$ acts by $(g\cdot x)(w)=x(w\circ g)$; thus the indicator $\delta_w$ of a word is sent to $\delta_{w\circ g^{-1}}$. A Young diagram $\lambda$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ ($i$ the row, $j$ the column) that is closed under moving up or to the left; $|\lambda|$ is its number of cells and $\ell(\lambda)$ its number of rows. A tableau of shape $\lambda$ on $[m]$ is a bijection $t:[m]\to\lambda$ (so $|\lambda|=m$). Its row word $r_t:[m]\to[\ell(\lambda)]$ sends $k$ to the row of $t(k)$; its column group $C_t\le S_m$ consists of the permutations $g$ such that $t(g(k))$ and $t(k)$ lie in the same column for every $k$; its polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\delta_{r_t}\in W_{m,\ell(\lambda)}$; and its Specht module $S^t\subseteq W_{m,\ell(\lambda)}$ is the $S_m$-invariant subspace spanned by $\{g\cdot e_t: g\in S_m\}$, with the restricted action. For a Young diagram $\lambda$ let $t_\lambda:[|\lambda|]\to\lambda$ be a fixed (canonical) tableau of shape $\lambda$, and write $S^\lambda=S^{t_\lambda}$.
--
--   *Strip chains.* Let $\mathbf b=(b_1,\dots,b_r)$ be a list of natural numbers and $\nu,\mu$ Young diagrams. A *sized strip chain* from $\nu$ to $\mu$ with sizes $\mathbf b$ is a chain $\nu=\mu_0\subseteq\mu_1\subseteq\dots\subseteq\mu_r=\mu$ of Young diagrams such that every $\mu_j/\mu_{j-1}$ is a *horizontal strip*, meaning that $\mu_j\setminus\mu_{j-1}$ contains at most one cell in each column, with $|\mu_j|=|\mu_{j-1}|+b_j$ ($1\le j\le r$). Empty strips ($b_j=0$) are allowed, and for $r=0$ the chain just says $\nu=\mu$.
--
--   Suppose there is a sized strip chain from $\nu$ to $\mu$ with sizes $(b_1,\dots,b_r)$, and let $\iota:[|\nu|]\to[|\mu|]$, $\iota(k)=t_\mu^{-1}(t_\nu(k))$, be the injective map sending a position of $t_\nu$ to the position of the same cell in $t_\mu$. Then there are a coloring $c:[|\mu|]\to\mathbb{N}$ and a linear map $F:S^\mu\to S^\nu$ such that:
--
--   1. $F$ is surjective;
--   2. $c(i)\le r$ for every position $i$;
--   3. $c(i)=0$ if and only if $i$ lies in the image of $\iota$;
--   4. for every $j\in\{1,\dots,r\}$, exactly $b_j$ positions have color $j$;
--   5. $F$ is equivariant for all color-preserving permutations compatible with $\iota$: for all $g$ and $h$ as below,
--
--   $$
--   c\circ g=c\ \text{ and }\ g\circ\iota=\iota\circ h\quad\Longrightarrow\quad F(g\cdot x)=h\cdot F(x)\ \text{ for all }x\in S^\mu\qquad(g\in S_{|\mu|},\ h\in S_{|\nu|}).
--   $$
--
--   So the nonzero colors split the positions outside $\iota([|\nu|])$ into classes of sizes $b_1,\dots,b_r$, and $F$ realizes $S^\nu$ as a quotient of $S^\mu$ restricted to the color-preserving permutations, with the permutations inside each nonzero color class acting trivially. This is an iterated form of the horizontal-strip Pieri rule; it is used to produce invariant functionals on Specht modules of dominant shapes (Young's rule).
--
--   **Formalization Note** The chain is the inductive predicate `SizedStripChain bs ν μ`, built by appending one strip at a time, and its inclusion $\nu\subseteq\mu$ is `hs.le`. With $0$-based list indexing `bs[j]` $=b_{j+1}$, so property 4 reads `(Finset.univ.filter (fun i => c i = j+1)).card = bs[j]` for `j < bs.length`. The canonical tableau is `shapeTableau λ = canonicalTableau λ rfl`, a fixed but unspecified enumeration of the cells, and $\iota$ is `tableauInclusion (shapeTableau ν) (shapeTableau μ) hs.le`. The theorem does not assert that the color classes are the cells of the individual strips; only their sizes are specified.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/SizedStrips.lean#L31-L114

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

theorem OAI.Saxl.stripChain_restriction {bs ν μ} (hs : SizedStripChain bs ν μ) :
    ∃ (c : Fin μ.card → ℕ) (F : Specht (shapeTableau μ) →ₗ[ℂ] Specht (shapeTableau ν)),
      Function.Surjective F ∧
      (∀ i, c i ≤ bs.length) ∧
      (∀ i, c i = 0 ↔ i ∈ Set.range (tableauInclusion (shapeTableau ν) (shapeTableau μ) hs.le)) ∧
      (∀ j (hj : j < bs.length), (Finset.univ.filter (fun i => c i = j+1)).card = bs[j]) ∧
      (∀ (g : Equiv.Perm (Fin μ.card)) (h : Equiv.Perm (Fin ν.card)),
        (∀ i, c (g i) = c i) →
        (∀ k, g (tableauInclusion (shapeTableau ν) (shapeTableau μ) hs.le k) =
          tableauInclusion (shapeTableau ν) (shapeTableau μ) hs.le (h k)) →
        ∀ x, F (spechtRep (shapeTableau μ) g x) = spechtRep (shapeTableau ν) h (F x)) := by sorry
