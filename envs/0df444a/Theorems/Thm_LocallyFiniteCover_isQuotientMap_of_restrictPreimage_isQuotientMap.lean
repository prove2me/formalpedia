-- Prove2me | Theorems.Thm_LocallyFiniteCover_isQuotientMap_of_restrictPreimage_isQuotientMap
-- name    : LocallyFiniteCover.isQuotientMap_of_restrictPreimage_isQuotientMap
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T19:43:05.071827+00:00
-- url     : https://prove2.me/theorems/6baa3421-ce1d-4d8b-b256-b9e105a1b9e2
-- title:
--   Quotient maps are local on the target for locally finite closed covers
-- statement:
--   **Locality of quotient maps for locally finite closed covers.** Let $X$ and $Y$ be topological spaces, let $f\colon X\to Y$ be a continuous map, and let $(A_i)_{i\in I}$ be a locally finite family of closed subsets of $Y$ with $\bigcup_{i\in I}A_i=Y$. For each $i$ let
--   $$f_i\colon f^{-1}(A_i)\longrightarrow A_i,\qquad x\longmapsto f(x),$$
--   be the restriction of $f$, where $f^{-1}(A_i)\subseteq X$ and $A_i\subseteq Y$ carry their subspace topologies. If every $f_i$ is a quotient map (that is, $f_i$ is surjective and a subset $U\subseteq A_i$ is open in $A_i$ if and only if $f_i^{-1}(U)$ is open in $f^{-1}(A_i)$), then $f$ is a quotient map:
--   $$f \text{ is surjective, and } U\subseteq Y \text{ is open} \iff f^{-1}(U)\subseteq X \text{ is open}.$$
--
--   Thus the property "the topology of $Y$ is the quotient topology induced by $f$" can be checked piece by piece on a locally finite closed cover of the target. The paper invokes this fact, citing Bourbaki, in the proof of Lemma 8.2.0.3 (pp. 385–386). There $F$ is a number field, $S$ a finite set of places of $F$ containing the archimedean ones, $\mathbf A_{F,S}=\prod_{v\in S}F_v$ and $\mathbf A_F$ are the $S$-adeles and the adeles of $F$, $\mathrm{GL}_1(\mathbf A_{F,S})^1$ and $\mathrm{GL}_1(\mathbf A_F)^1$ are the $S$-ideles and the ideles of norm one, $e_v$ is the ($S$-)adele with $v$-component $0$ and all other components $1$, and $Z_{F,S}=\{1\}\cup\{e_v\}_{v\in S}$, $Z_F=\{1\}\cup\{e_v\}_{v}$. In part (1) the fact is applied to the finite closed cover of $D^1_{F,S}=\mathrm{GL}_1(\mathbf A_{F,S})^1\cdot Z_{F,S}\subset\mathbf A_{F,S}$ by $D^1_{S,1}=\mathrm{GL}_1(\mathbf A_{F,S})^1$ and the sets $D^1_{S,v}=\mathrm{GL}_1(\mathbf A_{F,S})^1e_v$ ($v\in S$), and in part (2) to the closed cover of $D^1_F=\mathrm{GL}_1(\mathbf A_F)^1\cdot Z_F\subset\mathbf A_F$ by $D^1_1=\mathrm{GL}_1(\mathbf A_F)^1$ and the sets $D^1_v=\mathrm{GL}_1(\mathbf A_F)^1e_v$ ($v$ a place of $F$), to conclude that $D^1_{F,S}$, respectively $D^1_F$, carries the quotient topology of the multiplication map $(g,z)\mapsto gz$ from $\mathrm{GL}_1(\mathbf A_{F,S})^1\times Z_{F,S}$, respectively $\mathrm{GL}_1(\mathbf A_F)^1\times Z_F$. (In part (2) the cover is in fact not locally finite at the points of $D^1_1$: for $g\in D^1_1$ and a sequence of distinct finite places $v_n$ one has $g\,e_{v_n}\in D^1_{v_n}$ and $g\,e_{v_n}\to g$ in $\mathbf A_F$; the statement above is only the general topological tool, not a verification of that step.) It is a basic gluing tool for topological quotients and topological quotient stacks.
--
--   **Formalization Note.** The restriction $f_i$ is Mathlib's `Set.restrictPreimage (A i) f` and "quotient map" is `Topology.IsQuotientMap`. Continuity of $f$ is a hypothesis, as in the paper; it does not follow from the hypotheses on the $f_i$ (for $Y=\{a,b\}$ discrete with $A_1=\{a\}$, $A_2=\{b\}$, every restriction of a discontinuous surjection $[0,1]\to Y$ is a quotient map). Surjectivity of $f$ is not assumed because it follows from the surjectivity of the $f_i$ and $\bigcup_iA_i=Y$. The index type is arbitrary; an empty index type forces $Y=\varnothing$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 385–386, proof of Lemma 8.2.0.3(1),(2); classical reference (as cited by the paper at this spot): N. Bourbaki, Elements of Mathematics, General Topology, Springer, Ch. I, §5.1, Prop. 2, p. 51

import Mathlib

open Topology

set_option autoImplicit false

namespace LocallyFiniteCover

/-- Quotient maps are local on the target for locally finite closed covers: if `f : X → Y` is
continuous, `(A i)` is a locally finite family of closed subsets of `Y` covering `Y`, and each
restriction `f ⁻¹' A i → A i` is a quotient map, then `f` is a quotient map. -/
theorem isQuotientMap_of_restrictPreimage_isQuotientMap
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (A : ι → Set Y)
    (hA : LocallyFinite A) (hAc : ∀ i, IsClosed (A i)) (hAcov : ⋃ i, A i = Set.univ)
    (hq : ∀ i, IsQuotientMap ((A i).restrictPreimage f)) :
    IsQuotientMap f := by sorry

end LocallyFiniteCover
