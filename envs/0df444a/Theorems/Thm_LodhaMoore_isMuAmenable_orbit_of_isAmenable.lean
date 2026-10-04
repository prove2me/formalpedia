-- Prove2me | Theorems.Thm_LodhaMoore_isMuAmenable_orbit_of_isAmenable
-- name    : LodhaMoore.isMuAmenable_orbit_of_isAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T22:07:48.940433+00:00
-- url     : https://prove2.me/theorems/aa662774-ee9f-4641-9b70-c4a9162867aa
-- title:
--   Theorem 2.1 (external, Zimmer) — the orbit relation of a countable amenable group is μ-amenable
-- statement:
--   Let $\Gamma$ be a countable amenable group (`Garrido.IsAmenable`) acting by measurable maps on a Polish space $X$ with its Borel $\sigma$-algebra, and $\mu$ any $\sigma$-finite measure on $X$. Then the orbit equivalence relation $\{(x, y) : \exists g \in \Gamma,\ g \cdot x = y\}$ is $\mu$-amenable (`IsMuAmenable`).
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 4, Theorem 2.1

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_Garrido_Amenability

namespace LodhaMoore

theorem isMuAmenable_orbit_of_isAmenable {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    (Γ : Type) [Group Γ] [Countable Γ] [MulAction Γ X]
    (hmeas : ∀ g : Γ, Measurable fun x : X => g • x) (hΓ : Garrido.IsAmenable Γ) :
    IsMuAmenable μ {p : X × X | ∃ g : Γ, g • p.1 = p.2} := by
  sorry

end LodhaMoore
