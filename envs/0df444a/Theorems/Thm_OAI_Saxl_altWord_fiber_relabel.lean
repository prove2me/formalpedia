-- Prove2me | Theorems.Thm_OAI_Saxl_altWord_fiber_relabel
-- name    : OAI.Saxl.altWord_fiber_relabel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:02:04.206277+00:00
-- url     : https://prove2.me/theorems/033128a4-ac7a-4bba-aaec-ccf320c1ed53
-- title:
--   Relabelling positions in a signed alternation over a colour-preserving permutation group
-- statement:
--   Throughout, $[k]=\{0,1,\dots,k-1\}$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}$ is the complex vector space of all functions from such words to $\mathbb{C}$; it is the coordinate model of $(\mathbb{C}^d)^{\otimes n}$, the indicator $\mathbf{1}_a$ of a word playing the role of $e_{a(0)}\otimes\cdots\otimes e_{a(n-1)}$. The symmetric group $S_n$ acts on $W_{n,d}$ by permuting positions, $(g\cdot x)(a)=x(a\circ g)$, so that $g\cdot\mathbf{1}_a=\mathbf{1}_{a\circ g^{-1}}$. For a vector $v$ of a representation, $\langle v\rangle$ denotes the cyclic subrepresentation spanned by the orbit $\{g\cdot v\}$.
--
--   For a subgroup $G\le S_n$ and a word $a:[n]\to[d]$, the *signed alternation* of $a$ over $G$ is
--   $$A_G(a)=\sum_{g\in G}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_a\in W_{n,d},\qquad\text{so that}\qquad A_G(a)(v)=\sum_{g\in G}\operatorname{sgn}(g)\,[\,v\circ g=a\,],$$
--   where $[\,\cdot\,]$ is $1$ if the condition holds and $0$ otherwise.
--
--   For a map $c:[m]\to\alpha$ into an arbitrary set $\alpha$ (a colouring of the positions), let $\mathrm{Fib}(c)=\{g\in S_m:c\circ g=c\}$ be the group of permutations preserving every colour class, a Young subgroup of $S_m$.
--
--   **Theorem.** Let $n,m,d\in\mathbb{N}$, let $e:[n]\to[m]$ be a bijection, $c:[m]\to\alpha$ a colouring, $a:[m]\to[d]$ a word of length $m$ and $w:[n]\to[d]$ a word of length $n$. Then
--   $$A_{\mathrm{Fib}(c)}(a)\bigl(w\circ e^{-1}\bigr)=A_{\mathrm{Fib}(c\circ e)}(a\circ e)(w).$$
--
--   Signed alternations over the row group or the column group of a set of cells (the colouring being the row or the column of each cell) depend on the numbering of the positions only through this rule: renumbering by $e$ transports the colouring, the base word and the evaluation point simultaneously. It is used to rewrite the band layers of the staircase in a convenient path order of the band cells.
--
--   **Formalization Note** $A_G(a)$ is `altWord G a` and $\mathrm{Fib}(c)$ is `fiberGroup c`; $\alpha$ is an arbitrary type in a universe parameter, and the existence of the bijection $e$ forces $n=m$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/PathAlternation.lean#L163-L192

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

open OAI OAI.Saxl
open scoped TensorProduct
universe uAlpha

theorem OAI.Saxl.altWord_fiber_relabel {n m d : ℕ} {α : Type uAlpha}
    (e : Fin n ≃ Fin m) (c : Fin m → α) (a : Fin m → Fin d) (w : Fin n → Fin d) :
    altWord (fiberGroup c) a (w ∘ e.symm) =
      altWord (fiberGroup (c ∘ e)) (a ∘ e) w := by sorry
