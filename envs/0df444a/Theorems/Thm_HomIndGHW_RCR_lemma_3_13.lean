-- Prove2me | Theorems.Thm_HomIndGHW_RCR_lemma_3_13
-- name    : HomIndGHW.RCR.lemma_3_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:01:49.985385+00:00
-- url     : https://prove2.me/theorems/126183e9-f764-4792-90e2-382b46c386f7
-- title:
--   Lemma 3.13 — k-proRCR-equivalent targets have equal hom counts from connected structures with a full GHD of width ≤ k
-- statement:
--   Let $k\ge1$ and fix $\preceq_\sigma$. Let $\mathcal A$ be a finite connected $\sigma$-structure with a full GHD of width at most $k$, and let $\mathcal B,\mathcal B'$ be finite $\sigma$-structures with $\mathcal B\equiv_{k\text{-proRCR}}\mathcal B'$ (all without isolated elements). Then
--   $$\#\mathrm{Hom}(\mathcal A,\mathcal B)=\#\mathrm{Hom}(\mathcal A,\mathcal B').$$
--   This is the core of the direction (2) ⇒ (1) of Theorem 1.9.
--
--   Differences from the source:
--
--   - encoding: σ-structures, implicitly finite (#Hom is "the cardinality of a finite set", p. 14) → domains are types with [Fintype _]; relations are sets of tuples Fin (ar R) → V, hence finite; reason: finite domains are the paper's setting; a tuple of length ar(R) is a function on Fin (ar R)
--   - reading: σ-structures, which by Remark 2.1 (p. 14) and Remark 3.1 (p. 18) never have isolated elements → hypotheses A.NoIsolated, B.NoIsolated on every σ-structure of the statement; reason: the paper's standing assumption, stated once for the whole paper; the theorem's sentence relies on it
--   - encoding: a finite relational signature σ with positive arities and a fixed total order ⪯σ on its symbols → Sig (a finite type of symbols with ar_pos) and a [LinearOrder σ.Sym] binder; reason: the paper fixes an arbitrary total order (p. 6, p. 18); quantifying over every order covers each choice
--   - encoding: a GHD (T, B, λ) with T a tree, λ(v) a sequence of coloured tuples, width max |λ(v)| → GHD on a finite node type with T.IsTree, lam v : List (CT A), WidthLe k = ∀ v, (lam v).length ≤ k; condition (2) as Preconnected of the induced subgraph; reason: same objects; Preconnected lets an element in no bag impose nothing, and for structures without isolated elements every element lies in a bag by condition (1)
--   - encoding: C connected (not defined in the paper) → (gaifman C).Connected (Mathlib: connected and nonempty); reason: the standard reading; the empty structure has exactly one homomorphism into every structure and never separates two structures
--   - encoding: ≡_{k-proRCR} via the stable colouring χ_∞ and mult^A_k(c) = mult^B_k(c) for all stable colours c (Definition 1.7) → ProRCREquiv: for every round i and every canonical round-i colour c, the numbers of pro-tuples of A and of B with χ_i = c agree; reason: same all-rounds reading as for k-RCR (see the definition item)
--   - encoding: flat tuples and pro-tuples (α; t̄_1, …, t̄_m) with 1-based positions → flat tuples are List V; a pro-tuple is the pair (α, t̄_1 + ⋯ + t̄_m) as in §4; stp keeps the 1-based indices; reason: the arities in α recover the t̄_i, so the pair determines the pro-tuple
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 24, Lemma 3.13

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_GHD
import Definitions.Def_HomIndGHW_RCR_Refinement

open Classical HomIndGHW.RCR.Structure

namespace HomIndGHW.RCR

/-- Lemma 3.13 (p. 24): if `A` is connected and has a full GHD of width at most `k`, and
`B ≡_{k-proRCR} B′`, then `#Hom(A, B) = #Hom(A, B′)`. -/
theorem lemma_3_13 {σ : Sig} [LinearOrder σ.Sym] (k : ℕ) (hk : 1 ≤ k) {V W W' N : Type*}
    [Fintype V] [Fintype W] [Fintype W'] [Fintype N] (A : Structure σ V) (hA : A.NoIsolated)
    (hconn : A.Connected) (D : GHD A N) (hD : D.IsGHD) (hfull : D.Full) (hw : D.WidthLe k)
    (B : Structure σ W) (B' : Structure σ W') (hB : B.NoIsolated) (hB' : B'.NoIsolated)
    (hequiv : ProRCREquiv k B B') :
    homCount A B = homCount A B' := by sorry

end HomIndGHW.RCR
