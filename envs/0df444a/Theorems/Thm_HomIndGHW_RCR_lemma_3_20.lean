-- Prove2me | Theorems.Thm_HomIndGHW_RCR_lemma_3_20
-- name    : HomIndGHW.RCR.lemma_3_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:03:46.118694+00:00
-- url     : https://prove2.me/theorems/53d05d5c-cb5a-4c78-a7d8-ddad31395c98
-- title:
--   Lemma 3.20 — for a full and pure GHD, #Hom(A_D, B_split(B, k)) = #Hom(A_D, B(B, k)) = #Hom(A, B)
-- statement:
--   Let $k\ge1$, $\mathcal A$ a finite $\sigma$-structure and $D$ a full and pure GHD of $\mathcal A$ of width at most $k$ such that $\mathcal A_D$ has no isolated elements. For every finite $\sigma$-structure $\mathcal B$,
--   $$\#\mathrm{Hom}(\mathcal A_D,\mathcal B_{\mathrm{split}}(\mathcal B,k))=\#\mathrm{Hom}(\mathcal A_D,\mathcal B(\mathcal B,k))=\#\mathrm{Hom}(\mathcal A,\mathcal B).$$
--   (This is Lemma B.1, p. 51, with the first equality proved after Lemma 3.20.) For pure decompositions the binary encoding loses no homomorphism information.
--
--   Differences from the source:
--
--   - encoding: σ-structures, implicitly finite (#Hom is "the cardinality of a finite set", p. 14) → domains are types with [Fintype _]; relations are sets of tuples Fin (ar R) → V, hence finite; reason: finite domains are the paper's setting; a tuple of length ar(R) is a function on Fin (ar R)
--   - reading: σ-structures, which by Remark 2.1 (p. 14) and Remark 3.1 (p. 18) never have isolated elements → hypotheses A.NoIsolated, B.NoIsolated on every σ-structure of the statement; reason: the paper's standing assumption, stated once for the whole paper; the theorem's sentence relies on it
--   - encoding: a finite relational signature σ with positive arities and a fixed total order ⪯σ on its symbols → Sig (a finite type of symbols with ar_pos) and a [LinearOrder σ.Sym] binder; reason: the paper fixes an arbitrary total order (p. 6, p. 18); quantifying over every order covers each choice
--   - encoding: a GHD (T, B, λ) with T a tree, λ(v) a sequence of coloured tuples, width max |λ(v)| → GHD on a finite node type with T.IsTree, lam v : List (CT A), WidthLe k = ∀ v, (lam v).length ≤ k; condition (2) as Preconnected of the induced subgraph; reason: same objects; Preconnected lets an element in no bag impose nothing, and for structures without isolated elements every element lies in a bag by condition (1)
--   - encoding: Ord_λ(u): the tuples of λ(u) in increasing ⪯σ-order, ties unspecified (footnote 5) → a stable merge sort of λ(u) by symbol; reason: λ(u) is an arbitrary sequence, so every admissible ordering arises from some λ
--   - encoding: ε, a fresh dummy domain element → Option V with none for ε; reason: a fresh element is a disjoint extra point
--   - encoding: E_{i,j} for i, j ∈ {1, …, k·ar(σ)} → E indexed by Fin (k·ar σ) × Fin (k·ar σ), position i standing for the paper's i + 1; reason: a relabelling of the binary symbols of σ̂_k
--   - reading: A_D, a σ̂_k-structure, which by Remark 2.1 has no isolated elements; Definition 3.8 writes Ord_λ(u) = R_1(ā_1), …, R_ℓ(ā_ℓ) "where 1 ≤ ℓ ≤ k" → hypothesis (D.inducedBinary k).NoIsolated (for width ≤ k, equivalently every λ(u) is nonempty); reason: a node with empty λ(u) would be an isolated element of A_D with no admissible image in U_{Profile(u)}; the paper excludes it by its standing assumption and by 1 ≤ ℓ in Definition 3.8
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 27, Lemma 3.20 (= Lemma B.1, p. 51)

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_GHD
import Definitions.Def_HomIndGHW_RCR_Refinement
import Definitions.Def_HomIndGHW_RCR_Exploded
import Definitions.Def_HomIndGHW_RCR_InducedBinary

open Classical HomIndGHW.RCR.Structure

namespace HomIndGHW.RCR

/-- Lemma 3.20 = Lemma B.1 (p. 27, p. 51): for a full and pure GHD `D` of `A` of width at most `k`,
`#Hom(A_D, B_split(B, k)) = #Hom(A_D, B(B, k)) = #Hom(A, B)`. -/
theorem lemma_3_20 {σ : Sig} [LinearOrder σ.Sym] (k : ℕ) (hk : 1 ≤ k) {V W N : Type*}
    [Fintype V] [Fintype W] [Fintype N] (A : Structure σ V) (hA : A.NoIsolated) (D : GHD A N)
    (hD : D.IsGHD) (hfull : D.Full) (hpure : D.Pure) (hw : D.WidthLe k)
    (hAD : (D.inducedBinary k).NoIsolated) (B : Structure σ W) (hB : B.NoIsolated) :
    homCount (D.inducedBinary k) (splitExplode B k) = homCount (D.inducedBinary k) (explode B k) ∧
      homCount (D.inducedBinary k) (explode B k) = homCount A B := by sorry

end HomIndGHW.RCR
