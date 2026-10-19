-- Prove2me | Theorems.Thm_OAI_Saxl_irreducible_equiv_specht
-- name    : OAI.Saxl.irreducible_equiv_specht
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:14:42.22005+00:00
-- url     : https://prove2.me/theorems/4677ebda-e566-4f0d-bf6e-e74579848ab3
-- title:
--   Every irreducible complex representation of $S_n$ is isomorphic to a Specht module
-- statement:
--   Throughout, $[k]=\{0,1,\dots,k-1\}$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}$ is the complex vector space of all functions from such words to $\mathbb{C}$; it is the coordinate model of $(\mathbb{C}^d)^{\otimes n}$, the indicator $\mathbf{1}_a$ of a word playing the role of $e_{a(0)}\otimes\cdots\otimes e_{a(n-1)}$. The symmetric group $S_n$ acts on $W_{n,d}$ by permuting positions, $(g\cdot x)(a)=x(a\circ g)$, so that $g\cdot\mathbf{1}_a=\mathbf{1}_{a\circ g^{-1}}$. For a vector $v$ of a representation, $\langle v\rangle$ denotes the cyclic subrepresentation spanned by the orbit $\{g\cdot v\}$.
--
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) closed under moving up or to the left, and $\ell(\mu)$ is its number of rows. A tableau of shape $\mu$ on $n$ positions is a bijection $t:[n]\to\mu$. Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row of $t(i)$; its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$; its polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\mathbf{1}_{r_t}\in W_{n,\ell(\mu)}$; and its Specht module is the cyclic subrepresentation $S^t=\langle e_t\rangle\subseteq W_{n,\ell(\mu)}$.
--
--   For a partition $p$ of $n$ let $\lambda(p)$ be its Young diagram (row lengths the parts of $p$ in weakly decreasing order), $t_p$ a fixed tableau of shape $\lambda(p)$ on $n$ positions, and $S^p=S^{t_p}$ the corresponding Specht module, a representation of $S_n$ on a subspace of $W_{n,\ell(\lambda(p))}$.
--
--   **Theorem.** Let $V$ be a finite-dimensional complex vector space and $\rho$ an irreducible representation of $S_n$ on $V$ (so $V\neq0$ and its only invariant subspaces are $0$ and $V$). Then there is a partition $p$ of $n$ such that
--   $$\rho\;\cong\;S^p,$$
--   that is, there exists an $S_n$-equivariant linear isomorphism $V\to S^p$.
--
--   This is the completeness half of the classification of irreducible complex representations of the symmetric group: together with the irreducibility of Specht modules and the fact that different shapes give non-isomorphic Specht modules, it shows that the $S^p$, $p$ a partition of $n$, form a complete list of the irreducible representations up to isomorphism. In this development it is used to recognise every irreducible subrepresentation of a word space as a Specht module.
--
--   **Formalization Note** Partitions are Mathlib's `Nat.Partition n`, $t_p$ is `partitionTableau p` (the canonical tableau of `partitionDiagram p`), irreducibility is `Representation.IsIrreducible ρ`, and the conclusion is `Nonempty (ρ.Equiv (spechtRep (partitionTableau p)))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/SpechtClassification.lean#L170-L196

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

open OAI OAI.Saxl
open scoped TensorProduct
universe uV uG

theorem OAI.Saxl.irreducible_equiv_specht {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V)
    [Representation.IsIrreducible ρ] :
    ∃ p : Nat.Partition n, Nonempty (ρ.Equiv (spechtRep (partitionTableau p))) := by sorry
