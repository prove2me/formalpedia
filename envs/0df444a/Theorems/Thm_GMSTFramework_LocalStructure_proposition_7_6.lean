-- Prove2me | Theorems.Thm_GMSTFramework_LocalStructure_proposition_7_6
-- name    : GMSTFramework.LocalStructure.proposition_7_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:04:41.391197+00:00
-- url     : https://prove2.me/theorems/dd468c90-bf8b-4ac3-beb7-658f54db2b31
-- title:
--   Proposition 7.6 — a radial linkage for a cozy nest can be made orthogonal and end-identical [GSW25b]; $O(r|E|)$ algorithm
-- statement:
--   (Cited from [GSW25b] as printed in this paper.) Let $r\le s$. Let $(G,\Omega)$ be a society with a $\Sigma$-rendition $\rho$ with a cozy nest $\mathcal C$ of order $s$ and a radial linkage $\mathcal R$ of order $r$ for $\mathcal C$. Then there is a radial linkage $\mathcal R'$ of order $r$ for $\mathcal C$ that is orthogonal to $\mathcal C$ and end-identical to $\mathcal R$. Moreover an algorithm finds $\mathcal R'$ in time $O(r|E(G)|)$.
--
--   Differences from the source:
--   - encoding: s, r integers with r ≤ s → an additional hypothesis 0 < s; reason: a radial linkage for C is a V(Ω)-V(C₁)-linkage and is undefined when s = 0
--   - encoding: a Σ-rendition of the society (Σ with a single cuff) → X with IsSurface X and IsSocietyRendition ρ Ω (the boundary of X is one simple closed curve carrying V(Ω)); reason: renditions of societies are in surfaces with a single cuff (p. 16)
--   - reading: running time O(r|E(G)|) → at most C·(r·|E(G)| + 1); reason: at r = 0 the literal bound is 0, which no halting program meets; the additive constant is the usual meaning of O(·)
--   - encoding: "there exists an algorithm … in time O(r|E(G)|)" → one program P of the published word-RAM with oracle (CapacitatedKMedianFPT.Main: RunsTo, word-RAM time wordTime with the input word length, oracle calls counted separately) and one constant, for all inputs; the input is the self-delimiting encoding of the parameters, the labelled graph and the given objects (every description of a given cycle/rendition is accepted), and the output is a certificate (cell records of a rendition, vertex lists of paths, cycles, branch sets) of an object satisfying the conclusion; reason: topological objects cannot be input or output; the certificate fixes the combinatorial content and the conclusion asserts that a valid object realizing it exists; O(·) is a bound C·f with C independent of the input
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), Proposition 7.6, p. 60 (PDF 63)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Algorithms

open scoped Classical
open CapacitatedKMedianFPT.Main

namespace GMSTFramework.LocalStructure

/-- Proposition 7.6 ([GSW25b]): a radial linkage for a cozy nest can be replaced by an orthogonal,
end-identical one; with the algorithm. -/
theorem proposition_7_6 :
    (∀ s r : ℕ, r ≤ s → ∀ (hs : 0 < s) (X : Type) [TopologicalSpace X], IsSurface X →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (Ω : List V)
        (ρ : Rendition X (⊤ : G.Subgraph)), IsSocietyRendition ρ Ω →
      ∀ C : Nest ρ s, IsCozy Ω C →
      ∀ R : Linkage G r, IsRadialLinkage ρ Ω hs C.C R →
        ∃ R' : Linkage G r, IsRadialLinkage ρ Ω hs C.C R' ∧ RadialOrthogonal C.C R' ∧
          Linkage.EndIdentical R R') ∧
    (∃ (P : Program) (Cst : ℕ), ∀ s r : ℕ, r ≤ s → ∀ (hs : 0 < s) (X : Type)
        [TopologicalSpace X], IsSurface X →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        (label : V ≃ Fin (Fintype.card V)) (Ω : List V)
        (ρ : Rendition X (⊤ : G.Subgraph)), IsSocietyRendition ρ Ω →
      ∀ cells : List (List ℕ), DescribesRendition label ρ cells →
      ∀ C : Nest ρ s, IsCozy Ω C → ∀ cyc : Fin s → List ℕ,
        (∀ i, DescribesCycle label (C.C i) (cyc i)) →
      ∀ R : Linkage G r, IsRadialLinkage ρ Ω hs C.C R →
        ∃ out : List ℚ,
          RunsWithin P zeroOracle
            (encNats [s, r] ++ encGraph G (fun _ => ∅) label ++ encNats (Ω.map (vName label)) ++
              encNested cells ++ encNested (List.ofFn cyc) ++ encLinkage label R) out
            (Cst * (r * G.edgeSet.ncard + 1)) 0 ∧
          ∃ R' : Linkage G r, IsRadialLinkage ρ Ω hs C.C R' ∧ RadialOrthogonal C.C R' ∧
            Linkage.EndIdentical R R' ∧ out = encLinkage label R') := by sorry

end GMSTFramework.LocalStructure
