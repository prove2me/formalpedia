-- Prove2me | Theorems.Thm_GMSTFramework_LocalStructure_theorem_8_2
-- name    : GMSTFramework.LocalStructure.theorem_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:05:46.869237+00:00
-- url     : https://prove2.me/theorems/52b1378b-f8bb-47c4-9458-bf2d35fc9539
-- title:
--   Theorem 8.2 — homogeneous Local Structure Theorem: a controlled $K_t$-minor-model or a well-represented layout in a surface excluding $K_t$, with polynomial bounds and an oracle algorithm
-- statement:
--   There exist functions $\mathrm{boundary}:\mathbb N\to\mathbb N$, $\mathrm{apex},\mathrm{depth}:\mathbb N^4\to\mathbb N$, $\mathrm{breadth}:\mathbb N^3\to\mathbb N$ and $\mathrm{mesh}:\mathbb N^5\to\mathbb N$ such that for all integers $b\ge\mathrm{boundary}(t)$, $p\ge q\ge0$, $t\ge1$, $r\ge2$, $k\ge3$, $w\ge3$: for every $q$-colorful graph $(G,\chi)$, every $(b,q,p)$-colour-explorer $\varphi$ and every $\mathrm{mesh}(p,r,t,k,w)$-mesh $M\subseteq G$, either (i) $G$ has a $K_t$-minor model controlled by $M$, or (ii) $(G,\chi)$ has a well-represented $k$-$(\mathrm{apex}(p,r,t,k),\mathrm{breadth}(p,r,t),\mathrm{depth}(p,r,t,k),r,w)$-$\Sigma$-layout centred at $M$, where $\Sigma$ is a surface in which $K_t$ does not embed. Moreover $\mathrm{boundary}(t)\in O(t^{10})$, $\mathrm{apex}\in O((p+r+t+k)^{9620})$, $\mathrm{breadth}\in O((p+r+t)^{12})$, $\mathrm{depth}\in O((p+r+t+k)^{53144})$ and $\mathrm{mesh}\in O(p^{10}r^6w^6+(p+r+t+k)^{4852})$. There is also an algorithm that, given $p,r,t,k,w$, $(G,\chi)$ and $M$, with oracle access to $\varphi$, finds one of these outcomes in time $\mathrm{poly}(p+r+t+k+w)(|V(G)|+|E(G)|)|E(G)|^2$ with $O(t^2(|V(G)|+|E(G)|))$ calls to $\varphi$.
--
--   Semi-formal version: Theorem 1.2, p. 5–6 (PDF 8–9).
--
--   Differences from the source:
--   - reading: landscape/layout preamble "k, w ≥ 4", "k ≥ 4" against "k ≥ 3" in Theorem 8.2 → the preamble ranges are not conditions of the definitions; k ≥ 3 as in the theorem; reason: read literally no layout of detail 3 exists and the theorem fails at k = 3 (INSIGHTS I1)
--   - reading: L4 "D represents φ", defined only for non-empty I → Represents with J = I for every I; for I = ∅ condition i) forbids flap-segments; reason: the stronger of the two readings, matching Theorem 6.4 v) (INSIGHTS I2)
--   - reading: a landscape "of … breadth 𝖻, strength r, and depth d" in a k-(a, 𝖻, d, r, w′)-layout → breadth 𝖻′ ≤ 𝖻 and depth ≤ d, with the parameters a, 𝖻, d in w ≥ a + 𝖻(2d + 1) + 6 + w′; reason: the layout's parameters are bounds, like "|A| at most a" (Theorem 1.2: a homolst-near-embedding); exact breadth and depth breadth8.2, depth8.2 could exceed what G admits
--   - reading: "a Kt-minor model controlled by M" → controlled by the tangle T_M of M; reason: p. 13–14 define control for tangles and T_M for r-meshes
--   - generalization: φ a computable function satisfying the two axioms → φ any function satisfying the two axioms; reason: dropping computability enlarges the class of φ; the algorithm uses φ only as an oracle
--   - encoding: φ on boundaried graphs with arbitrary vertex sets; G with a fixed labelling → φ : BGraph → Finset ℕ on ℕ-vertex boundaried graphs, G's protrusions named by labels; the statement holds for every labelling label : V ≃ Fin |V|; reason: the axioms are invariant under renaming vertices, so every colour-explorer of the paper is covered with the same values
--   - encoding: "boundary(t) ∈ O(t¹⁰)" etc. → ∃ C, f(args) ≤ C·g(args) for all arguments in the theorem's range (t ≥ 1, r ≥ 2, k ≥ 3, w ≥ 3, p ≥ 0), one function serving all three parts; reason: uniform O-bounds on the same existentially chosen functions
--   - encoding: "a mesh8.2(p, r, t, k, w)-mesh" → in addition mesh(p, r, t, k, w) ≥ 2 on the theorem's range; reason: an n-mesh is defined only for n ≥ 2 (p. 13), so a smaller value names no mesh and would make the theorem vacuous; the paper's mesh8.2 (p. 87) is ≥ 535t³
--   - encoding: "there is an algorithm … finds one of these outcomes in time poly(p+r+t+k+w)(|V(G)|+|E(G)|)|E(G)|² with O(t²(|V(G)|+|E(G)|)) calls to φ" → one program P of the published word-RAM with oracle (CapacitatedKMedianFPT.Main), a polynomial poly and a constant C: on input (p, r, t, k, w, (G, χ), M) with the explorer oracle it halts within poly(p+r+t+k+w)·(|V|+|E|)·|E|² word-RAM steps and ≤ C·t²(|V|+|E|) oracle calls with a valid ModelCertificate or LayoutCertificate; reason: topological outputs are certified by their combinatorial content plus the existence of a realizing layout in some surface where K_t does not embed
--   - encoding: Σ a surface; Euler-genus, orientability → ∃ X : Type with a topology; HasEulerGenus and IsNonOrientable as homeomorphism relations to the polygon surfaces Σ(h, c); reason: Mathlib has no classification of surfaces
--   - encoding: traces of cycles ("pushed slightly") → trace relations; L5 and L7 required of every trace, L8 and hosting of some trace; reason: every property used is invariant under the push
--   - encoding: D ⊆ G an extended k-surface-wall (with hyperedges) → D⁻ embedded as a subdivision in G; hyperedge ends as further vertices of G; reason: p. 24: "D ⊆ G implicitly means D⁻ ⊆ G"
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), Theorem 8.2, p. 85 (PDF 88)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Layouts

open scoped Classical
open CapacitatedKMedianFPT.Main

namespace GMSTFramework.LocalStructure

/-- Theorem 8.2 (the homogeneous Local Structure Theorem): the five functions with their
polynomial bounds, the dichotomy, and the oracle algorithm. -/
theorem theorem_8_2 :
    ∃ (boundary : ℕ → ℕ) (apex depth : ℕ → ℕ → ℕ → ℕ → ℕ) (breadth : ℕ → ℕ → ℕ → ℕ)
      (mesh : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ),
      -- the O-bounds, uniform over the range of the theorem
      (∃ C : ℕ, ∀ t, 1 ≤ t → boundary t ≤ C * t ^ 10) ∧
      (∃ C : ℕ, ∀ p r t k, 1 ≤ t → 2 ≤ r → 3 ≤ k →
        apex p r t k ≤ C * (p + r + t + k) ^ 9620) ∧
      (∃ C : ℕ, ∀ p r t, 1 ≤ t → 2 ≤ r → breadth p r t ≤ C * (p + r + t) ^ 12) ∧
      (∃ C : ℕ, ∀ p r t k, 1 ≤ t → 2 ≤ r → 3 ≤ k →
        depth p r t k ≤ C * (p + r + t + k) ^ 53144) ∧
      (∃ C : ℕ, ∀ p r t k w, 1 ≤ t → 2 ≤ r → 3 ≤ k → 3 ≤ w →
        mesh p r t k w ≤ C * (p ^ 10 * r ^ 6 * w ^ 6 + (p + r + t + k) ^ 4852)) ∧
      -- a mesh8.2(p, r, t, k, w)-mesh is an n-mesh, defined for n ≥ 2 (p. 13)
      (∀ p r t k w, 1 ≤ t → 2 ≤ r → 3 ≤ k → 3 ≤ w → 2 ≤ mesh p r t k w) ∧
      -- the dichotomy
      (∀ b p q t r k w : ℕ, boundary t ≤ b → q ≤ p → 1 ≤ t → 2 ≤ r → 3 ≤ k → 3 ≤ w →
        ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (χ : V → Finset ℕ)
          (label : V ≃ Fin (Fintype.card V)), IsColorful q χ →
        ∀ φ : BGraph → Finset ℕ, IsColourExplorer b q p φ →
        ∀ M : Mesh G (mesh p r t k w) (mesh p r t k w),
          (∃ μ : (SimpleGraph.completeGraph (Fin t)).Minor G, ControlledBy μ M.tangle) ∨
          (∃ (X : Type) (_ : TopologicalSpace X),
            ¬ EmbedsIn (SimpleGraph.completeGraph (Fin t)) X ∧
            HasLayout b p φ G χ label M X k (apex p r t k) (breadth p r t) (depth p r t k) r w)) ∧
      -- the algorithm
      (∃ (P : Program) (poly : Polynomial ℕ) (C : ℕ),
        ∀ b p q t r k w : ℕ, boundary t ≤ b → q ≤ p → 1 ≤ t → 2 ≤ r → 3 ≤ k → 3 ≤ w →
        ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (χ : V → Finset ℕ)
          (label : V ≃ Fin (Fintype.card V)), IsColorful q χ →
        ∀ φ : BGraph → Finset ℕ, IsColourExplorer b q p φ →
        ∀ M : Mesh G (mesh p r t k w) (mesh p r t k w),
          ∃ out : List ℚ,
            RunsWithin P (explorerOracle φ)
              (encNats [p, r, t, k, w] ++ encGraph G χ label ++ encMesh label M) out
              (poly.eval (p + r + t + k + w) * (Fintype.card V + G.edgeSet.ncard) *
                G.edgeSet.ncard ^ 2)
              (C * (t ^ 2 * (Fintype.card V + G.edgeSet.ncard))) ∧
            (ModelCertificate t G label M out ∨
              LayoutCertificate b p t φ G χ label M k (apex p r t k) (breadth p r t)
                (depth p r t k) r w out)) := by sorry

end GMSTFramework.LocalStructure
