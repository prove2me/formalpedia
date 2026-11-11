-- Prove2me | Theorems.Thm_GMSTFramework_LocalStructure_proposition_7_8
-- name    : GMSTFramework.LocalStructure.proposition_7_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:04:33.807082+00:00
-- url     : https://prove2.me/theorems/f9a3b55a-2999-4b6e-a9e1-8c163812eee2
-- title:
--   Proposition 7.8 — splicing two orthogonal radial linkages across an interval of $r+2$ nest cycles [GSW25b]; $O(r|E|)$ algorithm
-- statement:
--   (Cited from [GSW25b] as printed in this paper.) Let $s,r,k,\ell$ be positive integers with $s\ge r+3$, $(G,\Omega)$ a society with a $\Sigma$-rendition $\rho$ and a nest $\mathcal C=\{C_1,\dots,C_s\}$, $\mathcal L,\mathcal R$ radial linkages of order $r$, both orthogonal to $\mathcal C$, and $I=[\ell,k]\subseteq[2,s]$ with $|I|=r+2$. Then there is a radial linkage $\mathcal P$ of order $r$ such that (i) $\mathcal P$ is orthogonal to $\{C_i:i\in[s]\setminus I\}$ with endpoints on $C_1$; (ii) $H_\ell\cap\bigcup\mathcal P\subseteq H_\ell\cap\bigcup\mathcal L$ for the inner graph $H_\ell$ of $C_\ell$, in particular the endpoints of $\mathcal P$ on $V(C_1)$ are those of $\mathcal L$; (iii) $H_k\cap\bigcup\mathcal P\subseteq H_k\cap\bigcup\mathcal R$ for the outer graph $H_k$ of $C_k$, in particular the endpoints of $\mathcal P$ on $V(\Omega)$ are those of $\mathcal R$. Moreover an algorithm finds $\mathcal P$ in time $O(r|E(G)|)$.
--
--   Differences from the source:
--   - encoding: cycles C₁, …, C_s and the interval I = [ℓ, k] ⊆ [2, s] with |I| = r + 2 → C.C ⟨i − 1, _⟩ = Cᵢ; hypotheses 2 ≤ ℓ, k ≤ s, k + 1 − ℓ = r + 2; reason: 0-based Fin indices; the same interval
--   - encoding: inner graph of C_ℓ, outer graph of C_k → for every boundary T of the stored nest disk (IsCDiskWith), the inclusions hold for innerGraph / outerGraph; reason: the disks of a nest are determined by their cycles
--   - encoding: "In particular" clauses → stated explicitly as equalities of the sets of ends of P and L on V(C₁), and of P and R on V(Ω); reason: consequences included verbatim
--   - encoding: a Σ-rendition of the society → X with IsSurface X and IsSocietyRendition ρ Ω; reason: renditions of societies are in surfaces with a single cuff
--   - encoding: "there exists an algorithm … in time O(r|E(G)|)" → one program P of the published word-RAM with oracle (CapacitatedKMedianFPT.Main: RunsTo, word-RAM time wordTime with the input word length, oracle calls counted separately) and one constant, for all inputs; the input is the self-delimiting encoding of the parameters, the labelled graph and the given objects (every description of a given cycle/rendition is accepted), and the output is a certificate (cell records of a rendition, vertex lists of paths, cycles, branch sets) of an object satisfying the conclusion; reason: topological objects cannot be input or output; the certificate fixes the combinatorial content and the conclusion asserts that a valid object realizing it exists; O(·) is a bound C·f with C independent of the input
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), Proposition 7.8, p. 61 (PDF 64)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Algorithms

open scoped Classical
open CapacitatedKMedianFPT.Main

namespace GMSTFramework.LocalStructure

/-- Proposition 7.8 ([GSW25b]): splicing two orthogonal radial linkages across the interval
`[ℓ, k]` of `r + 2` nest cycles (cycles `1`-based in the statement, `C.C ⟨i - 1, _⟩ = Cᵢ`); with the
algorithm. -/
theorem proposition_7_8 :
    (∀ (s r k ℓ : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (hk₁ : 1 ≤ k) (hℓ₁ : 1 ≤ ℓ) (hrs : r + 3 ≤ s)
        (hℓ : 2 ≤ ℓ) (hk : k ≤ s) (hI : k + 1 - ℓ = r + 2),
      ∀ (X : Type) [TopologicalSpace X], IsSurface X →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (Ω : List V)
        (ρ : Rendition X (⊤ : G.Subgraph)), IsSocietyRendition ρ Ω →
      ∀ C : Nest ρ s, ∀ L R : Linkage G r,
        IsRadialLinkage ρ Ω (by omega) C.C L → RadialOrthogonal C.C L →
        IsRadialLinkage ρ Ω (by omega) C.C R → RadialOrthogonal C.C R →
        ∃ P : Linkage G r, IsRadialLinkage ρ Ω (by omega) C.C P ∧
          -- i)
          (∀ i : Fin s, (i.val + 1 < ℓ ∨ k < i.val + 1) → ∀ j, IsPathSub (C.C i ⊓ (P.path j).sub)) ∧
          -- ii)
          (∀ T, ρ.IsCDiskWith (C.C ⟨ℓ - 1, by omega⟩) (C.disk ⟨ℓ - 1, by omega⟩) T →
            ρ.innerGraph (C.disk ⟨ℓ - 1, by omega⟩) (C.C ⟨ℓ - 1, by omega⟩) ⊓ P.sub ≤
              ρ.innerGraph (C.disk ⟨ℓ - 1, by omega⟩) (C.C ⟨ℓ - 1, by omega⟩) ⊓ L.sub) ∧
          {v | ∃ j, (v = (P.path j).s ∨ v = (P.path j).t) ∧ v ∈ (C.C ⟨0, by omega⟩).verts} =
            {v | ∃ j, (v = (L.path j).s ∨ v = (L.path j).t) ∧ v ∈ (C.C ⟨0, by omega⟩).verts} ∧
          -- iii)
          (∀ T, ρ.IsCDiskWith (C.C ⟨k - 1, by omega⟩) (C.disk ⟨k - 1, by omega⟩) T →
            ρ.outerGraph (C.disk ⟨k - 1, by omega⟩) T (C.C ⟨k - 1, by omega⟩) ⊓ P.sub ≤
              ρ.outerGraph (C.disk ⟨k - 1, by omega⟩) T (C.C ⟨k - 1, by omega⟩) ⊓ R.sub) ∧
          {v | ∃ j, (v = (P.path j).s ∨ v = (P.path j).t) ∧ v ∈ Ω} =
            {v | ∃ j, (v = (R.path j).s ∨ v = (R.path j).t) ∧ v ∈ Ω}) ∧
    (∃ (Pr : Program) (Cst : ℕ), ∀ (s r k ℓ : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) (hk₁ : 1 ≤ k)
        (hℓ₁ : 1 ≤ ℓ) (hrs : r + 3 ≤ s) (hℓ : 2 ≤ ℓ) (hk : k ≤ s) (hI : k + 1 - ℓ = r + 2),
      ∀ (X : Type) [TopologicalSpace X], IsSurface X →
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        (label : V ≃ Fin (Fintype.card V)) (Ω : List V)
        (ρ : Rendition X (⊤ : G.Subgraph)), IsSocietyRendition ρ Ω →
      ∀ cells : List (List ℕ), DescribesRendition label ρ cells →
      ∀ C : Nest ρ s, ∀ cyc : Fin s → List ℕ, (∀ i, DescribesCycle label (C.C i) (cyc i)) →
      ∀ L R : Linkage G r,
        IsRadialLinkage ρ Ω (by omega) C.C L → RadialOrthogonal C.C L →
        IsRadialLinkage ρ Ω (by omega) C.C R → RadialOrthogonal C.C R →
        ∃ out : List ℚ,
          RunsWithin Pr zeroOracle
            (encNats [s, r, k, ℓ] ++ encGraph G (fun _ => ∅) label ++
              encNats (Ω.map (vName label)) ++ encNested cells ++ encNested (List.ofFn cyc) ++
              encLinkage label L ++ encLinkage label R) out
            (Cst * (r * G.edgeSet.ncard)) 0 ∧
          ∃ P : Linkage G r, IsRadialLinkage ρ Ω (by omega) C.C P ∧
            (∀ i : Fin s, (i.val + 1 < ℓ ∨ k < i.val + 1) →
              ∀ j, IsPathSub (C.C i ⊓ (P.path j).sub)) ∧
            (∀ T, ρ.IsCDiskWith (C.C ⟨ℓ - 1, by omega⟩) (C.disk ⟨ℓ - 1, by omega⟩) T →
              ρ.innerGraph (C.disk ⟨ℓ - 1, by omega⟩) (C.C ⟨ℓ - 1, by omega⟩) ⊓ P.sub ≤
                ρ.innerGraph (C.disk ⟨ℓ - 1, by omega⟩) (C.C ⟨ℓ - 1, by omega⟩) ⊓ L.sub) ∧
            {v | ∃ j, (v = (P.path j).s ∨ v = (P.path j).t) ∧ v ∈ (C.C ⟨0, by omega⟩).verts} =
              {v | ∃ j, (v = (L.path j).s ∨ v = (L.path j).t) ∧ v ∈ (C.C ⟨0, by omega⟩).verts} ∧
            (∀ T, ρ.IsCDiskWith (C.C ⟨k - 1, by omega⟩) (C.disk ⟨k - 1, by omega⟩) T →
              ρ.outerGraph (C.disk ⟨k - 1, by omega⟩) T (C.C ⟨k - 1, by omega⟩) ⊓ P.sub ≤
                ρ.outerGraph (C.disk ⟨k - 1, by omega⟩) T (C.C ⟨k - 1, by omega⟩) ⊓ R.sub) ∧
            {v | ∃ j, (v = (P.path j).s ∨ v = (P.path j).t) ∧ v ∈ Ω} =
              {v | ∃ j, (v = (R.path j).s ∨ v = (R.path j).t) ∧ v ∈ Ω} ∧
            out = encLinkage label P) := by sorry

end GMSTFramework.LocalStructure
