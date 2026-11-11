-- Prove2me | Theorems.Thm_HomIndGHW_RCR_theorem_3_21
-- name    : HomIndGHW.RCR.theorem_3_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:03:16.356196+00:00
-- url     : https://prove2.me/theorems/0f94f95c-5d00-46ab-8bc4-2cfc340213e0
-- title:
--   Theorem 3.21 (Dvořák; Dell–Grohe–Rattan) — colour refinement vs homomorphism counts from structures whose Gaifman graph is a tree
-- statement:
--   Let $\sigma$ be a finite binary signature and $\mathcal A,\mathcal B$ finite binary $\sigma$-structures without isolated elements. Colour Refinement (1-WL of §2, with directed edge labels $\mu(v,w)$) distinguishes $\mathcal A$ and $\mathcal B$ if and only if there is a binary $\sigma$-structure $\mathcal T$ whose Gaifman graph is a tree with
--   $$\#\mathrm{Hom}(\mathcal T,\mathcal A)\neq\#\mathrm{Hom}(\mathcal T,\mathcal B).$$
--   The paper cites this result ([19, 18]) and applies it to the $k$-exploded encodings.
--
--   **Formalization Note.** Theorem 3.21 is a cited result ([19, 18]); it is stated here with the 1-WL of §2 (Remark 3.7), not the symmetric variant of [45].
--
--   Differences from the source:
--
--   - encoding: σ-structures, implicitly finite (#Hom is "the cardinality of a finite set", p. 14) → domains are types with [Fintype _]; relations are sets of tuples Fin (ar R) → V, hence finite; reason: finite domains are the paper's setting; a tuple of length ar(R) is a function on Fin (ar R)
--   - reading: σ-structures, which by Remark 2.1 (p. 14) and Remark 3.1 (p. 18) never have isolated elements → hypotheses A.NoIsolated, B.NoIsolated on every σ-structure of the statement; reason: the paper's standing assumption, stated once for the whole paper; the theorem's sentence relies on it
--   - encoding: a finite relational signature σ with positive arities → Sig (a finite type of symbols, arities with ar_pos); reason: same objects; the symbols are an arbitrary finite type
--   - encoding: ≡_{1-WL} (equal stable 1-WL colour multiplicities, §2 p. 15; not spelled out in the paper) → WLEquiv: for every round i and every canonical round-i colour c, the numbers of vertices with colour c agree; reason: same all-rounds reading as for k-RCR; 1-WL colours are canonical values
--   - encoding: "there is a σ-structure C" → ∃ n, ∃ C : Structure σ (Fin n); reason: every finite structure is isomorphic to one on Fin n, and hom counts are invariant under isomorphism
--   - encoding: "binary σ-structures" over a finite signature → σ : Sig with σ.IsBinary (every arity ≤ 2; arities are positive by Sig); reason: a binary structure has symbols of arity 1 and 2 (§2, p. 15)
--   - encoding: "the Gaifman graph of which is a tree" → (gaifman T).IsTree (Mathlib: connected, acyclic, nonempty); reason: a tree is nonempty
--   - reading: "There exists binary σ-structure T" (structures without isolated elements, Remark 2.1) → T.NoIsolated in the existential; reason: the standing assumption covers T; the only tree-shaped T it excludes is a single bare vertex, whose count |A| is, for A and B without isolated elements, already determined by the counts from stars without isolated elements
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 27, Theorem 3.21

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_Refinement
import Definitions.Def_HomIndGHW_RCR_Exploded

open Classical HomIndGHW.RCR.Structure

namespace HomIndGHW.RCR

/-- Theorem 3.21 (Dvořák; Dell–Grohe–Rattan; p. 27): for binary structures `A`, `B` over a finite
signature, Colour Refinement (1-WL of §2) distinguishes `A` and `B` iff some binary structure `T`
whose Gaifman graph is a tree has `#Hom(T, A) ≠ #Hom(T, B)`. -/
theorem theorem_3_21 {σ : Sig} (hbin : σ.IsBinary) {V W : Type*} [Fintype V] [Fintype W]
    (A : Structure σ V) (B : Structure σ W) (hA : A.NoIsolated) (hB : B.NoIsolated) :
    ¬ WLEquiv A B ↔
      ∃ (n : ℕ) (T : Structure σ (Fin n)), T.NoIsolated ∧ (gaifman T).IsTree ∧
        homCount T A ≠ homCount T B := by sorry

end HomIndGHW.RCR
