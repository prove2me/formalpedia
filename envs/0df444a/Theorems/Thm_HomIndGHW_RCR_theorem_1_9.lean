-- Prove2me | Theorems.Thm_HomIndGHW_RCR_theorem_1_9
-- name    : HomIndGHW.RCR.theorem_1_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:02:13.548223+00:00
-- url     : https://prove2.me/theorems/81464f54-d440-437b-90bc-a72f29cae686
-- title:
--   Theorem 1.9 — k-proRCR distinguishes A and B iff some connected structure of generalised hypertree width ≤ k separates their hom counts
-- statement:
--   Fix a finite signature $\sigma$ with positive arities and a total order $\preceq_\sigma$, and $k\ge1$. For finite $\sigma$-structures $\mathcal A,\mathcal B$ without isolated elements, the following are equivalent:
--
--   1. $k$-proRCR distinguishes $\mathcal A$ and $\mathcal B$, i.e. $\mathcal A\not\equiv_{k\text{-proRCR}}\mathcal B$;
--   2. there is a connected finite $\sigma$-structure $\mathcal C$ without isolated elements that admits a generalised hypertree decomposition of width at most $k$ with
--   $$\#\mathrm{Hom}(\mathcal C,\mathcal A)\neq\#\mathrm{Hom}(\mathcal C,\mathcal B).$$
--
--   Combined with Theorem 4.14 it gives the main theorem.
--
--   Differences from the source:
--
--   - encoding: σ-structures, implicitly finite (#Hom is "the cardinality of a finite set", p. 14) → domains are types with [Fintype _]; relations are sets of tuples Fin (ar R) → V, hence finite; reason: finite domains are the paper's setting; a tuple of length ar(R) is a function on Fin (ar R)
--   - reading: σ-structures, which by Remark 2.1 (p. 14) and Remark 3.1 (p. 18) never have isolated elements → hypotheses A.NoIsolated, B.NoIsolated on every σ-structure of the statement; reason: the paper's standing assumption, stated once for the whole paper; the theorem's sentence relies on it
--   - encoding: a finite relational signature σ with positive arities and a fixed total order ⪯σ on its symbols → Sig (a finite type of symbols with ar_pos) and a [LinearOrder σ.Sym] binder; reason: the paper fixes an arbitrary total order (p. 6, p. 18); quantifying over every order covers each choice
--   - encoding: ≡_{k-proRCR} via the stable colouring χ_∞ and mult^A_k(c) = mult^B_k(c) for all stable colours c (Definition 1.7) → ProRCREquiv: for every round i and every canonical round-i colour c, the numbers of pro-tuples of A and of B with χ_i = c agree; reason: same all-rounds reading as for k-RCR (see the definition item)
--   - encoding: flat tuples and pro-tuples (α; t̄_1, …, t̄_m) with 1-based positions → flat tuples are List V; a pro-tuple is the pair (α, t̄_1 + ⋯ + t̄_m) as in §4; stp keeps the 1-based indices; reason: the arities in α recover the t̄_i, so the pair determines the pro-tuple
--   - encoding: a GHD (T, B, λ) with T a tree, λ(v) a sequence of coloured tuples, width max |λ(v)| → GHD on a finite node type with T.IsTree, lam v : List (CT A), WidthLe k = ∀ v, (lam v).length ≤ k; condition (2) as Preconnected of the induced subgraph; reason: same objects; Preconnected lets an element in no bag impose nothing, and for structures without isolated elements every element lies in a bag by condition (1)
--   - encoding: C connected (not defined in the paper) → (gaifman C).Connected (Mathlib: connected and nonempty); reason: the standard reading; the empty structure has exactly one homomorphism into every structure and never separates two structures
--   - encoding: "there is a σ-structure C" → ∃ n, ∃ C : Structure σ (Fin n); reason: every finite structure is isomorphic to one on Fin n, and hom counts are invariant under isomorphism
--   - reading: "a connected σ-structure C" (Remark 2.1) → C.NoIsolated in the existential; reason: the standing assumption covers C; without it the statement fails (one isolated point vs two)
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 8, Theorem 1.9

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_GHD
import Definitions.Def_HomIndGHW_RCR_Refinement

open Classical HomIndGHW.RCR.Structure

namespace HomIndGHW.RCR

/-- Theorem 1.9 (p. 8): k-proRCR distinguishes `A` and `B` iff some connected `σ`-structure `C`
admitting a generalised hypertree decomposition of width at most `k` has
`#Hom(C, A) ≠ #Hom(C, B)`. -/
theorem theorem_1_9 {σ : Sig} [LinearOrder σ.Sym] (k : ℕ) (hk : 1 ≤ k) {V W : Type*}
    [Fintype V] [Fintype W] (A : Structure σ V) (B : Structure σ W) (hA : A.NoIsolated)
    (hB : B.NoIsolated) :
    ProRCRDistinguishes k A B ↔
      ∃ (n : ℕ) (C : Structure σ (Fin n)), C.NoIsolated ∧ C.Connected ∧ AdmitsGHD C k ∧
        homCount C A ≠ homCount C B := by sorry

end HomIndGHW.RCR
