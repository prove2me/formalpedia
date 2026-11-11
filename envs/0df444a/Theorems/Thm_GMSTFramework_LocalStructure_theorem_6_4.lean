-- Prove2me | Theorems.Thm_GMSTFramework_LocalStructure_theorem_6_4
-- name    : GMSTFramework.LocalStructure.theorem_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:05:17.629366+00:00
-- url     : https://prove2.me/theorems/4ae94eee-46e2-4bc5-9635-e78634a3ccf9
-- title:
--   Theorem 6.4 — initial representative surface-wall: sphere-rendition with one vortex and an extended $k$-surface-wall of signature $(0,0,f,1)$, $f\le4rp$, representing $\varphi$; oracle algorithm
-- statement:
--   There is a polynomial $\mathrm{mesh}_{6.4}:\mathbb N^3\to\mathbb N$ such that for all $k\ge3$, $r\ge1$, $p\ge q\ge0$, $b\ge3$, every $q$-colorful $(G,\chi)$, every $A\subseteq V(G)$ with $|A|+3\le b$, every flat $\mathrm{mesh}_{6.4}(k,r,p)$-mesh $M$ in $G-A$ and every $(b,q,p)$-colour-explorer $\varphi$, there are a sphere-rendition $\rho$ of $G-A$ with a unique vortex $c_0$ and an extended $k$-surface-wall $D$ with signature $(0,0,f,1)$, $f\le 4rp$, such that (i) $D$ is grounded in $\rho$; (ii) the tangle of $D$ is a truncation of the tangle of $M$; (iii) $\bar c_0$ lies in the interior of the disk bounded by the trace of the inner cycle of the vortex-segment of $D$ that avoids the simple cycle; (iv) $\rho$ is $I$-blank w.r.t. $\varphi$ and $A$ for $I=\bigcup\{\varphi(\mathrm{protrusion}_{\rho,A}(c)):c \text{ simple}\}\subseteq[p]$; (v) if $I\ne\emptyset$, $D$ represents $\varphi$ w.r.t. $A$ with strength $r$. Moreover an algorithm given $(G,\chi)$, $A$, $M$ and a sphere-rendition $\rho_0$ of $G-A$ witnessing the flatness of $M$, with oracle access to $\varphi$, outputs $\rho$, $D$, $I$ in time $\mathrm{poly}(p+k+r+b)(|V(G)|+|E(G)|)$ with $O(|V(G)|+|E(G)|)$ calls to $\varphi$.
--
--   Differences from the source:
--   - generalization: φ a computable function satisfying the singleton and preservation axioms → φ any function satisfying the two axioms; reason: dropping computability only enlarges the class of colour-explorers; the algorithm uses φ only through the oracle
--   - encoding: φ defined on boundaried graphs with arbitrary vertex sets, applied to boundaried subgraphs of G → φ : BGraph → Finset ℕ on boundaried graphs with vertices in ℕ; subgraphs of G passed with vertices named by their labels; reason: the axioms are invariant under renaming vertices, so every colour-explorer of the paper induces one here with the same values on G's protrusions
--   - encoding: D "in ρ", a rendition of G − A → D⁻ ≤ G − A and V(D) ∩ A = ∅; reason: implicit in "D is grounded in ρ"
--   - encoding: "there exists a polynomial function mesh6.4 : ℕ³ → ℕ" → mesh64 : MvPolynomial (Fin 3) ℕ evaluated at (k, r, p), with value ≥ 2 for k ≥ 3, r ≥ 1; reason: a polynomial with natural coefficients; a mesh6.4(k, r, p)-mesh is an n-mesh, defined only for n ≥ 2 (p. 13), and a smaller value would make the statement vacuous (the proof's mesh6.4 = homo6.3(s, ℓ) + 2 ≥ 2)
--   - encoding: "there exists an algorithm … in time poly(p + k + r + b)(|V(G)| + |E(G)|) with O(|V(G)| + |E(G)|) calls to φ (input also k, r, p)" → one program P of the published word-RAM with oracle (CapacitatedKMedianFPT.Main: RunsTo, word-RAM time wordTime with the input word length, oracle calls counted separately) and one constant, for all inputs; the input is the self-delimiting encoding of the parameters, the labelled graph and the given objects (every description of a given cycle/rendition is accepted), and the output is a certificate (cell records of a rendition, vertex lists of paths, cycles, branch sets) of an object satisfying the conclusion; reason: topological objects cannot be input or output; the certificate fixes the combinatorial content and the conclusion asserts that a valid object realizing it exists; O(·) is a bound C·f with C independent of the input
--   - encoding: traces, disks and the hyperedge of flap-segments → relations IsTraceCycle / IsDiskWithBoundary; hyperedge ends as a vertex set zs; reason: see the Renditions and SurfaceWalls definitions
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), Theorem 6.4, p. 51 (PDF 54)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_InitialWall

open scoped Classical
open CapacitatedKMedianFPT.Main

namespace GMSTFramework.LocalStructure

/-- Theorem 6.4 (an initial representative surface-wall), with the algorithm. -/
theorem theorem_6_4 :
    ∃ mesh64 : MvPolynomial (Fin 3) ℕ,
      (∀ k r p : ℕ, 3 ≤ k → 1 ≤ r → 2 ≤ MvPolynomial.eval ![k, r, p] mesh64) ∧
      (∀ k r p q b : ℕ, 3 ≤ k → 1 ≤ r → q ≤ p → 3 ≤ b →
        ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (χ : V → Finset ℕ)
          (label : V ≃ Fin (Fintype.card V)), IsColorful q χ →
        ∀ A : Finset V, A.card + 3 ≤ b →
        ∀ M : Mesh G (MvPolynomial.eval ![k, r, p] mesh64) (MvPolynomial.eval ![k, r, p] mesh64),
          IsFlatMesh (minusVerts G A) M →
        ∀ φ : BGraph → Finset ℕ, IsColourExplorer b q p φ →
          ∃ (ρ : Rendition TheSphere (minusVerts G A)) (D : SurfaceWall G k) (I : Finset ℕ),
            IsInitialWall b p φ G χ label A M k r ρ D I) ∧
      (∃ (P : Program) (poly : Polynomial ℕ) (C : ℕ),
        ∀ k r p q b : ℕ, 3 ≤ k → 1 ≤ r → q ≤ p → 3 ≤ b →
        ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (χ : V → Finset ℕ)
          (label : V ≃ Fin (Fintype.card V)), IsColorful q χ →
        ∀ A : Finset V, A.card + 3 ≤ b →
        ∀ M : Mesh G (MvPolynomial.eval ![k, r, p] mesh64) (MvPolynomial.eval ![k, r, p] mesh64),
        ∀ ρ₀ : Rendition TheSphere (minusVerts G A), WitnessesFlatMesh ρ₀ M →
        ∀ cells₀ : List (List ℕ), DescribesRendition label ρ₀ cells₀ →
        ∀ φ : BGraph → Finset ℕ, IsColourExplorer b q p φ →
          ∃ out : List ℚ,
            RunsWithin P (explorerOracle φ)
              (encNats [k, r, p] ++ encGraph G χ label ++ encNats (namesOf label (A : Set V)) ++
                encMesh label M ++ encNested cells₀) out
              (poly.eval (p + k + r + b) * (Fintype.card V + G.edgeSet.ncard))
              (C * (Fintype.card V + G.edgeSet.ncard)) ∧
            ∃ (ρ : Rendition TheSphere (minusVerts G A)) (D : SurfaceWall G k) (I : Finset ℕ)
              (cells : List (List ℕ)) (ks : List ℕ) (es zl : List (List ℕ)),
              IsInitialWall b p φ G χ label A M k r ρ D I ∧ DescribesRendition label ρ cells ∧
              DescribesWall label D ks es zl ∧
              out = encNested cells ++ encWall k ks es zl ++ encNats (sortedNats I)) := by sorry

end GMSTFramework.LocalStructure
