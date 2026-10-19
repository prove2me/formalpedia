-- Prove2me | Theorems.Thm_OAI_Saxl_altWord_letter_eval
-- name    : OAI.Saxl.altWord_letter_eval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:03:48.331286+00:00
-- url     : https://prove2.me/theorems/d2fa430a-8c14-47f0-a300-4e08f84099bc
-- title:
--   Signed alternations are unchanged under an injective relabelling of the letters
-- statement:
--   Throughout, $[k]=\{0,1,\dots,k-1\}$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}$ is the complex vector space of all functions from such words to $\mathbb{C}$; it is the coordinate model of $(\mathbb{C}^d)^{\otimes n}$, the indicator $\mathbf{1}_a$ of a word playing the role of $e_{a(0)}\otimes\cdots\otimes e_{a(n-1)}$. The symmetric group $S_n$ acts on $W_{n,d}$ by permuting positions, $(g\cdot x)(a)=x(a\circ g)$, so that $g\cdot\mathbf{1}_a=\mathbf{1}_{a\circ g^{-1}}$. For a vector $v$ of a representation, $\langle v\rangle$ denotes the cyclic subrepresentation spanned by the orbit $\{g\cdot v\}$.
--
--   For a subgroup $G\le S_n$ and a word $a:[n]\to[d]$, the *signed alternation* of $a$ over $G$ is
--   $$A_G(a)=\sum_{g\in G}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_a\in W_{n,d},\qquad\text{so that}\qquad A_G(a)(v)=\sum_{g\in G}\operatorname{sgn}(g)\,[\,v\circ g=a\,],$$
--   where $[\,\cdot\,]$ is $1$ if the condition holds and $0$ otherwise.
--
--   **Theorem.** Let $n,d,D\in\mathbb{N}$, let $\varphi:[d]\to[D]$ be injective, let $G\le S_n$ be a subgroup and let $a,w:[n]\to[d]$ be words. Then
--   $$A_G(\varphi\circ a)(\varphi\circ w)=A_G(a)(w),$$
--   where the left-hand side is computed in $W_{n,D}$ and the right-hand side in $W_{n,d}$.
--
--   Embedding a small alphabet into a larger one (for example the two letters $\{0,1\}$ into the row indices of a larger Young diagram) therefore does not change the coefficients of a signed alternation on words that only use the embedded letters. This is used to compare the band layers of the staircase, whose letters lie in a two-letter subalphabet, with the alternating two-letter words of a path.
--
--   **Formalization Note** $A_G(a)$ is `altWord G a`, an element of `WordSpace n d`, i.e. a function `(Fin n → Fin d) → ℂ` evaluated at a word.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/PathAlternation.lean#L194-L210

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

theorem OAI.Saxl.altWord_letter_eval {n d D : ℕ} (φ : Fin d → Fin D) (hφ : Function.Injective φ)
    (G : Subgroup (Equiv.Perm (Fin n))) (a w : Fin n → Fin d) :
    altWord G (φ ∘ a) (φ ∘ w) = altWord G a w := by sorry
