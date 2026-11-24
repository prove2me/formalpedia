-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_Supplement_theorem_13
-- name    : Gomory69.Asymptotic.Supplement.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:26:17.4894+00:00
-- url     : https://prove2.me/theorems/a23af592-e2c8-43e0-8e2e-4afaf80125e0
-- title:
--   THEOREM 13 — Facet extension and vertex restriction (corrected: reverse implication fails)
-- statement:
--   Let $G$ be a finite Abelian group, $N\subseteq G\setminus\{0\}$ and $g_0\in G$. Write $j_N$ for extension by zero from $\mathbb R^N$ to $\mathbb R^{G^+}$ and $E(N)$ for its image. The corner polyhedron $P(G,N,g_0)$ is the hull of all nonnegative integer solutions (the zero solution included at $g_0=0$); the master polyhedron $P(G,g_0)$ excludes the zero solution (p. 474 footnote).
--
--   (a) If $g_0\ne0$ or $|G|\ne2$, every corner facet $(\pi,\pi_0)$ has a master facet extension $(\pi',\pi_0)$ with $\pi'|_N=\pi$.
--
--   (b) Every nonzero vertex of the corner polyhedron extends to a master vertex:
--   $$x\in\operatorname{ext}P(G,N,g_0),\ x\ne0\ \Longrightarrow\ j_Nx\in\operatorname{ext}P(G,g_0).$$
--
--   (c) For every master vertex $x$: if $x=j_Ny$ for a corner vertex $y$ then $x\in E(N)$; and when $g_0\ne0$, conversely every master vertex in $E(N)$ is $j_Ny$ for a corner vertex $y$.
--
--   (d) The printed reverse facet implication fails: for $G=\mathbb Z/4$, $g_0=3$, $N=\{2,3\}$, the master inequality $t(1)+2t(2)+3t(3)\ge3$ is a facet, but its restriction $2t(2)+3t(3)\ge3$ is not a corner facet. Both assertions are part of the Lean conclusion.
--
--   The exclusions in (a)–(c) are exactly the cases where the incompatible zero conventions make the printed clauses false: at $G=\mathbb Z/2$, $N=\{1\}$, $g_0=0$ the corner hull is $[0,\infty)$ with facet $t\ge0$ and vertex $0$, while the master hull is $[2,\infty)$ with only the facet $t\ge2$ and vertex $2$.
--
--   Differences from the source:
--   - correction: part (i) is an iff, with the master face called (D-1)-dimensional → retain forward facet extension and both vertex clauses, and explicitly refute the reverse implication in ZMod 4; reason: p. 476 says that restrictions may be superfluous; the given master facet restricts to a hyperplane with only one tight point in a two-dimensional corner space; face throughout p. 468 means facet, of dimension D-2
--   - correction: no zero-target exception is printed → facet extension assumes g0 nonzero or card G not 2; the forward vertex clause assumes the corner vertex is nonzero; the converse vertex-restriction direction assumes g0 nonzero; reason: p. 474 removes the master origin while the corner hull keeps it; in ZMod 2 at target zero each excluded case fails (facet t>=0 without master extension, vertex 0 outside the master hull, master vertex 2 not a corner vertex); at target zero with card G not 2 the corner facets are the t(h)>=0 and extend by THEOREM 16
--   - encoding: vertices of the corner and master are compared in one ambient space → use zero extension and existential inverse image for vertex restriction; reason: p. 475 explicitly identifies the corner space with E(N)
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), DOI 10.1016/0024-3795(69)90017-2, p. 476, THEOREM 13

import Mathlib
import Definitions.Def_Gomory69_MasterFaces_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_Supplement_CoordinateSection

namespace Gomory69.Asymptotic.Supplement

/-- Corrected THEOREM 13. Facet extension holds except at target zero in the group of order
two; the forward vertex clause holds for every nonzero corner vertex; the vertex-restriction
criterion holds in the trivial direction always and in the converse direction at nonzero target;
and the printed reverse facet implication is refuted by an explicit example. -/
theorem theorem_13 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : 0 ∉ N) (g₀ : G) :
    ((g₀ ≠ 0 ∨ Fintype.card G ≠ 2) →
      ∀ (π : N → ℝ) (π₀ : ℝ), Gomory69.MasterFaces.IsFace N g₀ π π₀ →
        ∃ π' : Gomory69.Lifting.Plus G → ℝ,
          Gomory69.Lifting.IsFace G g₀ π' π₀ ∧
          ∀ g : N, Gomory69.Lifting.ext π' (g : G) = π g) ∧
    (∀ x : N → ℝ, x ∈ Set.extremePoints ℝ (groupPolyhedron N g₀) → x ≠ 0 →
      zeroExtend N x ∈ Set.extremePoints ℝ (Gomory69.Lifting.P G g₀)) ∧
    (∀ x ∈ Set.extremePoints ℝ (Gomory69.Lifting.P G g₀),
      (∃ y ∈ Set.extremePoints ℝ (groupPolyhedron N g₀), zeroExtend N y = x) →
        x ∈ coordinateSpace N) ∧
    (g₀ ≠ 0 → ∀ x ∈ Set.extremePoints ℝ (Gomory69.Lifting.P G g₀),
      x ∈ coordinateSpace N →
        ∃ y ∈ Set.extremePoints ℝ (groupPolyhedron N g₀), zeroExtend N y = x) ∧
    (Gomory69.Lifting.IsFace (ZMod 4) 3
        (fun g => ((g : ZMod 4).val : ℝ)) 3 ∧
      ¬ Gomory69.MasterFaces.IsFace ({2, 3} : Finset (ZMod 4)) 3
        (fun g => ((g : ZMod 4).val : ℝ)) 3) := by sorry

end Gomory69.Asymptotic.Supplement
