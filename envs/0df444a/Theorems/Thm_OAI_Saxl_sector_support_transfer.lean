-- Prove2me | Theorems.Thm_OAI_Saxl_sector_support_transfer
-- name    : OAI.Saxl.sector_support_transfer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:10:57.164634+00:00
-- url     : https://prove2.me/theorems/dea5dd69-f557-455f-b857-50f3e961946e
-- title:
--   Averaging a sector-equivariant, sector-supported map into a cyclic word module gives a nonzero intertwiner
-- statement:
--   Throughout, $[k]=\{0,1,\dots,k-1\}$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}$ is the complex vector space of all functions from such words to $\mathbb{C}$; it is the coordinate model of $(\mathbb{C}^d)^{\otimes n}$, the indicator $\mathbf{1}_a$ of a word playing the role of $e_{a(0)}\otimes\cdots\otimes e_{a(n-1)}$. The symmetric group $S_n$ acts on $W_{n,d}$ by permuting positions, $(g\cdot x)(a)=x(a\circ g)$, so that $g\cdot\mathbf{1}_a=\mathbf{1}_{a\circ g^{-1}}$. For a vector $v$ of a representation, $\langle v\rangle$ denotes the cyclic subrepresentation spanned by the orbit $\{g\cdot v\}$.
--
--   Let $D\subseteq[n]$ be a set of positions and $A\subseteq[d]$ a set of letters. The *word sector* $\Sigma(D,A)$ is the set of words $w:[n]\to[d]$ with $w(i)\in A\iff i\in D$ for every position $i$, and $\mathrm{Stab}(D)=\{g\in S_n:g(i)\in D\iff i\in D\ \text{for all }i\}$ is the stabiliser of $D$.
--
--   **Theorem.** Let $X$ be a complex vector space carrying a representation $\rho$ of $S_n$ (no finiteness assumption), let $D\subseteq[n]$, $A\subseteq[d]$, $z\in W_{n,d}$, and let $f:X\to W_{n,d}$ be a nonzero linear map such that
--
--   1. $f$ is equivariant for the stabiliser of $D$: $f(\rho(g)x)=g\cdot f(x)$ for all $g\in\mathrm{Stab}(D)$ and $x\in X$;
--   2. $f$ takes values in the cyclic module of $z$: $f(x)\in\langle z\rangle$ for all $x\in X$;
--   3. $f$ is supported on the sector: $f(x)(w)\neq0$ implies $w\in\Sigma(D,A)$, for all $x\in X$ and all words $w$.
--
--   Then there exists a nonzero $S_n$-equivariant linear map
--   $$F:X\longrightarrow\langle z\rangle .$$
--
--   This is an induction tool: a map that is equivariant only for the permutations preserving a set of positions, and whose values live on the corresponding coordinate sector, can be averaged over the whole symmetric group without cancellation. It is used to transport constituents found for a block of positions (such as the band of a staircase) to the full cyclic module.
--
--   **Formalization Note** $\Sigma(D,A)$ is `wordSector D A`, $\mathrm{Stab}(D)$ is `sectorGroup D`, $D$ and $A$ are predicates on `Fin n` and `Fin d`, and $F$ is a `Representation.IntertwiningMap` into the subrepresentation `cyclic (wordRep n d) z`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/CyclicSector.lean#L103-L152

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

open OAI OAI.Saxl
open scoped TensorProduct
universe uG uX uY uZ uV

theorem OAI.Saxl.sector_support_transfer {n d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (D : Fin n → Prop) (A : Fin d → Prop) (z : WordSpace n d)
    (f : X →ₗ[ℂ] WordSpace n d) (hf : f ≠ 0)
    (he : ∀ g ∈ sectorGroup D, ∀ x, f (ρ g x) = wordRep n d g (f x))
    (hm : ∀ x, f x ∈ cyclic (wordRep n d) z)
    (hs : ∀ x w, f x w ≠ 0 → wordSector D A w) :
    ∃ F : Representation.IntertwiningMap ρ (cyclic (wordRep n d) z).toRepresentation,
      F ≠ 0 := by sorry
