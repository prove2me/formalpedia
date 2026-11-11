-- Prove2me | Theorems.Thm_GMSTFramework_LocalStructure_proposition_7_5
-- name    : GMSTFramework.LocalStructure.proposition_7_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:04:31.893207+00:00
-- url     : https://prove2.me/theorems/60a818de-b7c9-4da1-8aee-85c90cff8d84
-- title:
--   Proposition 7.5 — every nest can be replaced by a cozy nest of the same order inside $C_1$ and its outer graph [GSW25b, Lemma 8.4]; $O(s|E|^2)$ algorithm
-- statement:
--   (Cited from [GSW25b, Lemma 8.4] as printed in this paper.) Let $s\ge1$, $(G,\Omega)$ a society and $\rho$ a rendition of $(G,\Omega)$ in the disk with a nest $\mathcal C=\{C_1,\dots,C_s\}$. Then there is a cozy nest $\mathcal C'$ of order $s$ in $(G,\Omega)$ such that $C_1$ together with the outer graph of $C_1$ in $\rho$ contains $\bigcup\mathcal C'$. Moreover an algorithm finds $\mathcal C'$ in time $O(s|E(G)|^2)$.
--
--   Differences from the source:
--   - encoding: the outer graph of C₁ (defined through the C₁-disk) → for every boundary T of the stored C₁-disk with IsCDiskWith, ⋃C′ ≤ C₁ ⊔ outerGraph; reason: the C₁-disk of a disk rendition is unique, so its boundary is
--   - encoding: a cozy nest C′ "in (G, Ω)" → a Nest of the same rendition ρ (with its C′ᵢ-disks) satisfying IsCozy; reason: coziness is defined relative to the rendition ρ
--   - encoding: "there exists an algorithm … in time O(s|E(G)|²)" → one program P of the published word-RAM with oracle (CapacitatedKMedianFPT.Main: RunsTo, word-RAM time wordTime with the input word length, oracle calls counted separately) and one constant, for all inputs; the input is the self-delimiting encoding of the parameters, the labelled graph and the given objects (every description of a given cycle/rendition is accepted), and the output is a certificate (cell records of a rendition, vertex lists of paths, cycles, branch sets) of an object satisfying the conclusion; reason: topological objects cannot be input or output; the certificate fixes the combinatorial content and the conclusion asserts that a valid object realizing it exists; O(·) is a bound C·f with C independent of the input
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), Proposition 7.5, p. 60 (PDF 63)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Algorithms

open scoped Classical
open CapacitatedKMedianFPT.Main

namespace GMSTFramework.LocalStructure

/-- Proposition 7.5 ([GSW25b, Lemma 8.4]): every nest can be replaced by a cozy nest of the same
order inside `C₁` and its outer graph; with the algorithm. -/
theorem proposition_7_5 :
    (∀ (s : ℕ) (hs : 1 ≤ s),
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (Ω : List V)
        (ρ : Rendition TheDisk (⊤ : G.Subgraph)), IsSocietyRendition ρ Ω →
      ∀ C : Nest ρ s,
        ∃ C' : Nest ρ s, IsCozy Ω C' ∧
          ∀ T, ρ.IsCDiskWith (C.C ⟨0, by omega⟩) (C.disk ⟨0, by omega⟩) T →
            cyclesSub C'.C ≤ C.C ⟨0, by omega⟩ ⊔
              ρ.outerGraph (C.disk ⟨0, by omega⟩) T (C.C ⟨0, by omega⟩)) ∧
    (∃ (P : Program) (Cst : ℕ), ∀ (s : ℕ) (hs : 1 ≤ s),
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        (label : V ≃ Fin (Fintype.card V)) (Ω : List V)
        (ρ : Rendition TheDisk (⊤ : G.Subgraph)), IsSocietyRendition ρ Ω →
      ∀ cells : List (List ℕ), DescribesRendition label ρ cells →
      ∀ C : Nest ρ s, ∀ cyc : Fin s → List ℕ, (∀ i, DescribesCycle label (C.C i) (cyc i)) →
        ∃ out : List ℚ,
          RunsWithin P zeroOracle
            (encNats [s] ++ encGraph G (fun _ => ∅) label ++ encNats (Ω.map (vName label)) ++
              encNested cells ++ encNested (List.ofFn cyc)) out
            (Cst * (s * G.edgeSet.ncard ^ 2)) 0 ∧
          ∃ (C' : Nest ρ s) (cyc' : Fin s → List ℕ), IsCozy Ω C' ∧
            (∀ T, ρ.IsCDiskWith (C.C ⟨0, by omega⟩) (C.disk ⟨0, by omega⟩) T →
              cyclesSub C'.C ≤ C.C ⟨0, by omega⟩ ⊔
                ρ.outerGraph (C.disk ⟨0, by omega⟩) T (C.C ⟨0, by omega⟩)) ∧
            (∀ i, DescribesCycle label (C'.C i) (cyc' i)) ∧ out = encNested (List.ofFn cyc')) := by sorry

end GMSTFramework.LocalStructure
