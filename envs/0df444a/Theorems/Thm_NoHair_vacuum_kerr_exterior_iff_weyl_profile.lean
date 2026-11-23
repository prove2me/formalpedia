-- Prove2me | Theorems.Thm_NoHair_vacuum_kerr_exterior_iff_weyl_profile
-- name    : NoHair.vacuum_kerr_exterior_iff_weyl_profile
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:00:09.425831+00:00
-- url     : https://prove2.me/theorems/39563751-c774-428f-a087-a77c70b2b3a2
-- title:
--   Characterization of the vacuum Kerr exterior by a Weyl representation and its rod boundary profile
-- statement:
--   Fix vacuum Kerr parameters $m>0$, $a^2\le m^2$, and a domain on which the electromagnetic field vanishes. The domain is a Kerr exterior with these parameters if and only if there is a global exterior comparison chart with a vacuum Ernst solution reconstructing the metric in its local Weyl charts and obeying the normalized estimates for the rod profile with half-length $\sqrt{m^2-a^2}$ and angular momentum $ma$. The reverse implication uses elliptic boundary uniqueness and continuity across the rotation axis. The characterization includes $a=0$ and the extremal parameter values.
-- source:
--   P. T. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Astérisque 321 (2008), §§6.2–6.7, https://arxiv.org/abs/0806.0016. P. O. Mazur, Proof of uniqueness of the Kerr–Newman black hole solution, J. Phys. A 15 (1982) 3173–3180, doi:10.1088/0305-4470/15/10/021. The explicit coordinate statement below uses the mission’s normalized axial Ernst potentials and Weyl chart reconstruction.

import Definitions.Def_NoHair_weylBoundaryProfile

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.vacuum_kerr_exterior_iff_weyl_profile {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ,E4) ∞ M] (g F : BilinField M) (D : Set M) (m a : ℝ)
    (hm : IsKerrNewmanBlackHoleParams m a 0) (hF : ∀ x ∈ D, F x = 0) :
    IsKerrNewmanDOC g F D m a 0 ↔
      ∃ (Ψ : E4 → M) (u : Weyl.ErnstPotentials),
        IsDiffeoOnto Ψ (kerrNewmanDOC m a 0) D ∧ u.IsSolution ∧
        Weyl.IsWeylRepresentation m a (pullbackCoeffs g Ψ) u ∧
        Weyl.HasProfileEstimates u (Weyl.rodBoundaryProfile m (Real.sqrt (m^2-a^2)) (m*a)) := by
  sorry
