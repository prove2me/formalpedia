-- Prove2me | Theorems.Thm_FourColorLinear_main_types_count
-- name    : FourColorLinear.main_types_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:27.665962+00:00
-- url     : https://prove2.me/theorems/cdccdfa2-6567-41ac-bced-c7ae230fa0a9
-- title:
--   The number of main types is at most $6k$, and $\partial R^{\mathcal{KC}}_{G_R}$ has size $O(|\partial R|)$
-- statement:
--   There is an absolute $C$ such that for each plane triangulation, each coloring of the complement of a family of pairwise non-touching connected nonempty vertex sets $Z$, and each color pairing:
--
--   1. for each set $\vec K$ of $k$ Kempe chains, at most $6k$ main types relative to $\vec K$ occur;
--   2. for each region $R$, the number of vertices of $\partial R$, plus the number of Kempe nodes of $\partial R^{\mathcal K}_G$, plus the number of main types of the $Z\subseteq R-\partial R$ relative to the chains meeting $\partial R$, is at most $C(|\partial R|+1)$.
--
--   This is why swap decisions on a batch of chains can use only $O(k)$ counters, though $\Omega(n)$ configurations may touch one chain.
--
--   Differences from the source:
--   - generalization: reducible configurations → pairwise non-touching connected vertex sets off the colored part; reason: the argument contracts them; reducible configurations are such sets
--   - reading: "O(k)" → at most 6k; reason: the proof applies Lemma 12, whose bound is 6q
--   - reading: ∂R^{KC}_{G_R} "has size O(|∂R|)" → its vertices are counted: ∂R, Kempe nodes, configuration nodes; reason: it is a plane graph, so its edges are at most thrice as many
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), §3, p.20; p.22

import Mathlib
import Definitions.Def_FourColorLinear_contr
import Definitions.Def_FourColorLinear_IsRegion
import Definitions.Def_FourColorLinear_IsKempeChangeOn
import Definitions.Def_FourColorLinear_mainTypes

open PlanarQueue.Genus

namespace FourColorLinear

/-- The count of main types, arXiv:2610.39753 (held version, sha256 4dce39c5…), p.20: "the main type of such a reducible configuration Z is the
set of Kempe chains from K⃗ that Z touches. We claim that the number of main types relative to K⃗ is
only O(k)." With p.22: "The number of main configuration types is thus O(|∂R|) and we already know that
∂R^K_G has size O(|∂R|), so we conclude that ∂R^{KC}_{GR} has size O(|∂R|)."

**Formalization Note** The configurations are pairwise non-touching connected vertex sets off the
colored part, all the proof uses of them, so this covers reducible configurations. The absolute `6` is
from Lemma 12. The size of `∂R^{KC}_{GR}` is counted in vertices: `∂R`, Kempe nodes, configuration nodes;
it is a plane graph, so its edges are at most thrice that. -/
theorem main_types_count :
    ∃ C : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
      (S : EmbeddingScheme G), IsPlaneTriangulation S →
      ∀ (ψ : V → Fin 4) (p : Fin 3) (Zs : Set (Set V)),
        (∀ Z ∈ Zs, Z.Nonempty ∧ (G.induce Z).Preconnected) →
        (∀ Z ∈ Zs, ∀ Z' ∈ Zs, Z ≠ Z' → ¬ Touch G Z Z') →
        let W : Set V := (⋃₀ Zs)ᶜ
        ProperOn G W ψ →
        (∀ Ks : Set (Set V), (∀ K ∈ Ks, IsKempeChain G W ψ p K) →
          (mainTypes G Ks Zs).ncard ≤ 6 * Ks.ncard) ∧
        ∀ E : Set (Sym2 V), IsRegion G E →
          let dv := boundaryVerts S E
          let de := boundaryEdges S E
          let Ks : Set (Set V) := {K | IsKempeChain G W ψ p K ∧ (K ∩ dv).Nonempty}
          dv.ncard + Nat.card (contr S (kempeEdges G W ψ p) dv de Set.univ).Node +
              (mainTypes G Ks {Z | Z ∈ Zs ∧ Z ⊆ edgeVerts E \ dv}).ncard ≤ C * (dv.ncard + 1) := by sorry

end FourColorLinear
