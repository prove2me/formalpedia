-- Prove2me | Theorems.Thm_HomIndGHW_RCR_remark_2_4
-- name    : HomIndGHW.RCR.remark_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:01:33.19766+00:00
-- url     : https://prove2.me/theorems/4d5e0bce-1f0d-4c11-b689-f1884a158a43
-- title:
--   Remark 2.4 — every GHD or FHD can be made full with the same width, keeping (semi-)purity
-- statement:
--   Let $\mathcal A$ be a finite $\sigma$-structure without isolated elements. For every generalised hypertree decomposition $D=(T,B,\lambda)$ of $\mathcal A$ there is a **full** GHD $D'$ of $\mathcal A$ with
--   $$\mathrm{width}(D')=\mathrm{width}(D),\qquad |V(T')|\le|V(T)|+|\mathrm{CT}(\mathcal A)|,$$
--   and $D'$ is pure whenever $D$ is. The same holds for fractional hypertree decompositions, where moreover $D'$ is semi-pure whenever $D$ is. (Construction: for every coloured tuple $R(\bar t)$ violating fullness, attach to a node $v$ with $\mathrm{set}(\bar t)\subseteq B(v)$ a new child $v'$ with $B(v')=\mathrm{set}(\bar t)$, $\lambda(v')=(R(\bar t))$.)
--
--   This normalisation lets every later argument assume fullness without loss of generality.
--
--   Differences from the source:
--
--   - encoding: σ-structures, implicitly finite (#Hom is "the cardinality of a finite set", p. 14) → domains are types with [Fintype _]; relations are sets of tuples Fin (ar R) → V, hence finite; reason: finite domains are the paper's setting; a tuple of length ar(R) is a function on Fin (ar R)
--   - reading: σ-structures, which by Remark 2.1 (p. 14) and Remark 3.1 (p. 18) never have isolated elements → hypotheses A.NoIsolated, B.NoIsolated on every σ-structure of the statement; reason: the paper's standing assumption, stated once for the whole paper; the theorem's sentence relies on it
--   - encoding: a finite relational signature σ with positive arities → Sig (a finite type of symbols, arities with ar_pos); reason: same objects; the symbols are an arbitrary finite type
--   - encoding: a GHD (T, B, λ) with T a tree, λ(v) a sequence of coloured tuples, width max |λ(v)| → GHD on a finite node type with T.IsTree, lam v : List (CT A), WidthLe k = ∀ v, (lam v).length ≤ k; condition (2) as Preconnected of the induced subgraph; reason: same objects; Preconnected lets an element in no bag impose nothing, and for structures without isolated elements every element lies in a bag by condition (1)
--   - reading: "the resulting decomposition has size that is linear in the size of the original one" → the new decomposition has at most |V(T)| + |CT(A)| nodes; reason: the construction adds one node per coloured tuple violating fullness, and |CT(A)| ≤ |σ|·(number of tuples), which is the paper's justification
--   - encoding: "(semi-)pure" → pure for GHDs; pure and semi-pure for FHDs; reason: semi-purity is defined for FHDs only (p. 17)
--   - encoding: the output decomposition on an unspecified tree → node type Fin m; reason: every finite tree is isomorphic to one on Fin m
-- source:
--   Aivasiliotis, Chen, Göbel, Lanzinger, Roth, Schneider, Homomorphism Indistinguishability Beyond Graphs, consolidated manuscript (catalogued as arXiv:2607.07934; sha256 671ba611…), p. 17, Remark 2.4

import Mathlib
import Definitions.Def_HomIndGHW_RCR_Structures
import Definitions.Def_HomIndGHW_RCR_GHD

open Classical HomIndGHW.RCR.Structure

namespace HomIndGHW.RCR

/-- Remark 2.4 (p. 17): every generalised (resp. fractional) hypertree decomposition can be made
full with the same width, by attaching for each coloured tuple `R(t̄)` violating (b) a child `v′`
with `B(v′) = set(t̄)`, `λ(v′) = (R(t̄))` to a node `v` with `set(t̄) ⊆ B(v)`; the result has at most
`|V(T)| + |CT(A)|` nodes, and it is pure (resp. semi-pure) when the original one is. -/
theorem remark_2_4 {σ : Sig} {V : Type*} [Fintype V] (A : Structure σ V) (hA : A.NoIsolated) :
    (∀ {N : Type*} [Fintype N] (D : GHD A N), D.IsGHD →
      ∃ (m : ℕ) (D' : GHD A (Fin m)), D'.IsGHD ∧ D'.Full ∧ D'.width = D.width ∧
        m ≤ Fintype.card N + Fintype.card (CT A) ∧ (D.Pure → D'.Pure)) ∧
    (∀ {N : Type*} [Fintype N] (D : FHD A N), D.IsFHD →
      ∃ (m : ℕ) (D' : FHD A (Fin m)), D'.IsFHD ∧ D'.Full ∧ D'.width = D.width ∧
        m ≤ Fintype.card N + Fintype.card (CT A) ∧ (D.Pure → D'.Pure) ∧
        (D.SemiPure → D'.SemiPure)) := by sorry

end HomIndGHW.RCR
