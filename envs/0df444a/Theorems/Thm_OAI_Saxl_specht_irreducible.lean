-- Prove2me | Theorems.Thm_OAI_Saxl_specht_irreducible
-- name    : OAI.Saxl.specht_irreducible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T23:57:37.661914+00:00
-- url     : https://prove2.me/theorems/5bbd9dc0-37d6-4534-9a10-3a0cf3c89795
-- title:
--   Complex Specht modules of the symmetric group are irreducible
-- statement:
--   Let $\mu$ be a Young diagram with $d$ rows, $n\in\mathbb{N}$, and $t$ a tableau of shape $\mu$, i.e. a bijection from the positions $[n]=\{0,\dots,n-1\}$ to the cells of $\mu$ (so $n=|\mu|$). Let $W_{n,d}$ be the space of functions on words $[n]\to[d]$ with $S_n$ acting by $(g\cdot x)(a)=x(a\circ g)$, and let
--   $$e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot e_{r_t}$$
--   be the polytabloid of $t$, where $r_t$ is the row word ($r_t(p)$ is the row of $t(p)$) and $C_t$ the group of column-preserving permutations. The Specht module $S^t=\operatorname{span}_{\mathbb{C}}\{g\cdot e_t:g\in S_n\}\subseteq W_{n,d}$, with the restricted action, is an irreducible complex representation of $S_n$:
--   $$S^t\neq0\qquad\text{and}\qquad U=0\ \text{ or }\ U=S^t\ \text{ for every } S_n\text{-invariant subspace } U\subseteq S^t .$$
--
--   Irreducibility is what makes Specht modules usable as test objects: by Schur's lemma a nonzero intertwiner between two of them is an isomorphism, and every nonzero intertwiner out of $S^t$ is injective. It is used throughout the analysis of the tensor square of the staircase Specht module, for example to identify Specht modules up to a sign twist and to lift intertwiners.
--
--   **Formalization Note** Irreducibility is Mathlib's `Representation.IsIrreducible` for `spechtRep t`, i.e. the lattice of subrepresentations is a simple order (exactly two elements, $\bot\neq\top$). The proof works over $\mathbb{C}$ with complex conjugation of coordinates; no general semisimplicity theorem is used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/SpechtSubmodule.lean#L196-L226

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule

open OAI OAI.Saxl
open scoped TensorProduct
universe uG uV

theorem OAI.Saxl.specht_irreducible {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Representation.IsIrreducible (spechtRep t) := by sorry
