-- Prove2me | Theorems.Thm_HomIndGHW_RCR_proposition_3_5
-- name    : HomIndGHW.RCR.proposition_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:02:43.229206+00:00
-- url     : https://prove2.me/theorems/fd362181-677d-4bc0-acc4-ee53532a9670
-- title:
--   Proposition 3.5 — the split and plain k-exploded encodings are 1-WL-equivalent together
-- statement:
--   For a total order $\preceq_\sigma$, $k\ge1$ and finite $\sigma$-structures $\mathcal A,\mathcal B$ without isolated elements,
--   $$\mathcal B_{\mathrm{split}}(\mathcal A,k)\equiv_{1\text{-WL}}\mathcal B_{\mathrm{split}}(\mathcal B,k)\iff\mathcal B(\mathcal A,k)\equiv_{1\text{-WL}}\mathcal B(\mathcal B,k).$$
--   It allows the proof to switch freely between the two encodings.
--
--   Differences from the source:
--
--   - encoding: σ-structures, implicitly finite (#Hom is "the cardinality of a finite set", p. 14) → domains are types with [Fintype _]; relations are sets of tuples Fin (ar R) → V, hence finite; reason: finite domains are the paper's setting; a tuple of length ar(R) is a function on Fin (ar R)
--   - reading: σ-structures, which by Remark 2.1 (p. 14) and Remark 3.1 (p. 18) never have isolated elements → hypotheses A.NoIsolated, B.NoIsolated on every σ-structure of the statement; reason: the paper's standing assumption, stated once for the whole paper; the theorem's sentence relies on it
--   - encoding: a finite relational signature σ with positive arities and a fixed total order ⪯σ on its symbols → Sig (a finite type of symbols with ar_pos) and a [LinearOrder σ.Sym] binder; reason: the paper fixes an arbitrary total order (p. 6, p. 18); quantifying over every order covers each choice
--   - encoding: E_{i,j} for i, j ∈ {1, …, k·ar(σ)} → E indexed by Fin (k·ar σ) × Fin (k·ar σ), position i standing for the paper's i + 1; reason: a relabelling of the binary symbols of σ̂_k
--   - encoding: ≡_{1-WL} (equal stable 1-WL colour multiplicities, §2 p. 15; not spelled out in the paper) → WLEquiv: for every round i and every canonical round-i colour c, the numbers of vertices with colour c agree; reason: same all-rounds reading as for k-RCR; 1-WL colours are canonical values
--   - encoding: flat tuples and pro-tuples (α; t̄_1, …, t̄_m) with 1-based positions → flat tuples are List V; a pro-tuple is the pair (α, t̄_1 + ⋯ + t̄_m) as in §4; stp keeps the 1-based indices; reason: the arities in α recover the t̄_i, so the pair determines the pro-tuple
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 20, Proposition 3.5

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_Refinement
import Definitions.Def_HomIndGHW_RCR_Exploded

open Classical HomIndGHW.RCR.Structure

namespace HomIndGHW.RCR

/-- Proposition 3.5 (p. 20): `B_split(A, k) ≡_{1-WL} B_split(B, k)` iff
`B(A, k) ≡_{1-WL} B(B, k)`. -/
theorem proposition_3_5 {σ : Sig} [LinearOrder σ.Sym] (k : ℕ) (hk : 1 ≤ k) {V W : Type*}
    [Fintype V] [Fintype W] (A : Structure σ V) (B : Structure σ W) (hA : A.NoIsolated)
    (hB : B.NoIsolated) :
    WLEquiv (splitExplode A k) (splitExplode B k) ↔ WLEquiv (explode A k) (explode B k) := by sorry

end HomIndGHW.RCR
