-- Prove2me | Theorems.Thm_OAI_Saxl_word_support_separates
-- name    : OAI.Saxl.word_support_separates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:16:54.761256+00:00
-- url     : https://prove2.me/theorems/d4eb61a9-0a7e-4901-8f8f-ea5bf1b75304
-- title:
--   A representation containing every Specht type of height at most $d$ separates the vectors of $(\mathbb{C}^d)^{\otimes n}$
-- statement:
--   Throughout, $[k]=\{0,1,\dots,k-1\}$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}$ is the complex vector space of all functions from such words to $\mathbb{C}$; it is the coordinate model of $(\mathbb{C}^d)^{\otimes n}$, the indicator $\mathbf{1}_a$ of a word playing the role of $e_{a(0)}\otimes\cdots\otimes e_{a(n-1)}$. The symmetric group $S_n$ acts on $W_{n,d}$ by permuting positions, $(g\cdot x)(a)=x(a\circ g)$, so that $g\cdot\mathbf{1}_a=\mathbf{1}_{a\circ g^{-1}}$. For a vector $v$ of a representation, $\langle v\rangle$ denotes the cyclic subrepresentation spanned by the orbit $\{g\cdot v\}$.
--
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) closed under moving up or to the left, and $\ell(\mu)$ is its number of rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$. Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of $t(i)$; its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$; its polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_{r_t}\in W_{n,\ell(\mu)}$; and its Specht module is the cyclic subrepresentation $S^t=\langle e_t\rangle\subseteq W_{n,\ell(\mu)}$.
--
--   **Theorem.** Let $n,d\in\mathbb{N}$ and let $\sigma$ be a representation of $S_n$ on a complex vector space $V$ (no finiteness assumption). Assume that for every Young diagram $\mu$ with $\ell(\mu)\le d$ and every tableau $t$ of shape $\mu$ on $n$ positions there is a nonzero $S_n$-equivariant linear map $S^t\to V$. Then for every nonzero $x\in W_{n,d}$ there is an $S_n$-equivariant linear map $f:W_{n,d}\to V$ with
--   $$f(x)\neq0 .$$
--
--   So a representation that contains every irreducible type of height at most $d$, with any multiplicities, detects every vector of $(\mathbb{C}^d)^{\otimes n}$. This is the bridge from statements of the form "every small Specht module occurs in a given cyclic module" to statements about arbitrary vectors of word spaces.
--
--   **Formalization Note** $V$ carries `σ : Representation ℂ (Equiv.Perm (Fin n)) V`, the hypothesis quantifies over all `YoungDiagram`s with `μ.colLen 0 ≤ d` and all tableaux `t : Tableau n μ`, and $f$ is a `Representation.IntertwiningMap (wordRep n d) σ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/SupportSeparation.lean#L130-L156

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

open OAI OAI.Saxl
open scoped TensorProduct
universe uR uX uY uG uV

theorem OAI.Saxl.word_support_separates {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (h : ∀ (μ : YoungDiagram) (t : Tableau n μ), μ.colLen 0 ≤ d →
      ∃ f : Representation.IntertwiningMap (spechtRep t) σ, f ≠ 0)
    (x : WordSpace n d) (hx : x ≠ 0) :
    ∃ f : Representation.IntertwiningMap (wordRep n d) σ, f x ≠ 0 := by sorry
