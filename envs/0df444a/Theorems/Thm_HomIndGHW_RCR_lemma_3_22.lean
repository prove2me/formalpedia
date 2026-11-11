-- Prove2me | Theorems.Thm_HomIndGHW_RCR_lemma_3_22
-- name    : HomIndGHW.RCR.lemma_3_22
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:03:53.561183+00:00
-- url     : https://prove2.me/theorems/f68efe42-fb6e-43de-9ab9-1a8540dfa771
-- title:
--   Lemma 3.22 — k-proRCR-inequivalence yields a structure with a pure full GHD of width ≤ k separating hom counts
-- statement:
--   Let $k\ge1$, fix $\preceq_\sigma$, and let $\mathcal B,\mathcal B'$ be finite $\sigma$-structures without isolated elements with $\mathcal B\not\equiv_{k\text{-proRCR}}\mathcal B'$. Then there are a finite $\sigma$-structure $\mathcal A$ and a pure full GHD $D$ of $\mathcal A$ of width at most $k$ (with $\mathcal A$ and $\mathcal A_D$ free of isolated elements) such that
--   $$\#\mathrm{Hom}(\mathcal A_D,\mathcal B_{\mathrm{split}}(\mathcal B,k))\neq\#\mathrm{Hom}(\mathcal A_D,\mathcal B_{\mathrm{split}}(\mathcal B',k)),$$
--   and consequently $\#\mathrm{Hom}(\mathcal A,\mathcal B)\neq\#\mathrm{Hom}(\mathcal A,\mathcal B')$. $\mathcal A$ need not be connected. This is the core of the direction (1) ⇒ (2) of Theorem 1.9.
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
--   - encoding: ≡_{k-proRCR} via the stable colouring χ_∞ and mult^A_k(c) = mult^B_k(c) for all stable colours c (Definition 1.7) → ProRCREquiv: for every round i and every canonical round-i colour c, the numbers of pro-tuples of A and of B with χ_i = c agree; reason: same all-rounds reading as for k-RCR (see the definition item)
--   - encoding: "there is a σ-structure C" → ∃ n, ∃ C : Structure σ (Fin n); reason: every finite structure is isomorphic to one on Fin n, and hom counts are invariant under isomorphism
--   - reading: "There exists a σ-structure A and a pure full GHD D for A" (structures without isolated elements by Remark 2.1) → the witnesses also satisfy A.NoIsolated and (D.inducedBinary k).NoIsolated; reason: the standing assumption applies to A and to the σ̂_k-structure A_D; the paper's construction (one tuple block per node, λ(v) of length ℓ_v ∈ [k]) satisfies both
--   - encoding: the decomposition on the tree of T → node type Fin m; reason: every finite tree is isomorphic to one on Fin m
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 27, Lemma 3.22

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_GHD
import Definitions.Def_HomIndGHW_RCR_Refinement
import Definitions.Def_HomIndGHW_RCR_Exploded
import Definitions.Def_HomIndGHW_RCR_InducedBinary

open Classical HomIndGHW.RCR.Structure

namespace HomIndGHW.RCR

/-- Lemma 3.22 (p. 27): if `B ≢_{k-proRCR} B′`, there are a structure `A` and a pure full GHD `D`
of `A` of width at most `k` with `#Hom(A_D, B_split(B, k)) ≠ #Hom(A_D, B_split(B′, k))`; consequently
`#Hom(A, B) ≠ #Hom(A, B′)`. (`A` and `A_D` are free of isolated elements, the standing assumption of
Remark 2.1.) -/
theorem lemma_3_22 {σ : Sig} [LinearOrder σ.Sym] (k : ℕ) (hk : 1 ≤ k) {W W' : Type*}
    [Fintype W] [Fintype W'] (B : Structure σ W) (B' : Structure σ W') (hB : B.NoIsolated)
    (hB' : B'.NoIsolated) (hdist : ProRCRDistinguishes k B B') :
    ∃ (n : ℕ) (A : Structure σ (Fin n)) (m : ℕ) (D : GHD A (Fin m)),
      A.NoIsolated ∧ D.IsGHD ∧ D.Pure ∧ D.Full ∧ D.WidthLe k ∧
      (D.inducedBinary k).NoIsolated ∧
      homCount (D.inducedBinary k) (splitExplode B k) ≠
        homCount (D.inducedBinary k) (splitExplode B' k) ∧
      homCount A B ≠ homCount A B' := by sorry

end HomIndGHW.RCR
