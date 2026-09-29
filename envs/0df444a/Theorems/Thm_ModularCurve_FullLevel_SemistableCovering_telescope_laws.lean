-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_telescope_laws
-- name    : ModularCurve.FullLevel.SemistableCovering.telescope_laws
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/4c05995a-d9d2-5a6a-bf84-29895054865f
-- title:
--   Telescope laws of a semistable covering at full level
-- statement:
--   Fix a prime $q$, a nonzero natural number $M'$, a valuation subring $A$ of $\overline{\mathbb Q}$ with residue field $\kappa =$ `ResidueField A`, and a finite set $W$ of places of $\kappa$-function field `modularFunctionFieldC κ M'`. Let $\mathcal C$ be a `SemistableCovering q M' A W` of $F =$ `fieldBar q M'` (the constant extension to $\overline{\mathbb Q}$ of the function field of $X_H$ of level $q^2M'$, $H$ the kernel of $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$), let $\pi \in A$, and assume: the width clause for $\pi$ (each $(\mathcal C.\mathrm{An}\,\ell\,s)$ has modulus a unit times a positive power of $\pi$), the genus clause, the disc-fibre clause and the curve clause. The conclusion asserts eleven statements about the re-indexed telescope, with $N = \#(\mathbb P^1(\mathbb F_q) \sqcup W)$ components and $M = \#(\mathbb P^1(\mathbb F_q)\times W)$ edges: $g(F)+N = \sum_{i<N} g(\bar F_i) + M + 1$; each $\bar F_i$ is a curve over $\kappa$ and essentially of finite type over $\kappa$, has principal divisors, and all its places are $\kappa$-rational; each chart $C_i$ has disc fibres over its non-nodal places, i.e. for $Q \notin C_i.\mathrm{nodes}$ there is $T$ in $C_i.\mathrm{integers}$ with nonzero residue of order $1$ at $Q$, with $T$ lying in the valuation ring of every $P \in C_i.\mathrm{dom}$ above $Q$ and $P.\mathrm{evalAt}\,T$ in the maximal ideal of $A$, and with exactly one such $P$ for each prescribed value $c$ in that maximal ideal; for each edge $e$, $1 \le w_\pi(e)$ and the modulus of $A_e$ is a unit times $\pi^{w_\pi(e)}$; $A_e$ and $A'_e$ share domain and modulus, that modulus is nonzero, and the two parameters multiply to its image in $F$; $A_e$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $A'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$; every node of every chart is an end of exactly one edge; and every place of $F$ over $\overline{\mathbb Q}$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain.
--
--   This packages the data and clauses of a bundled semistable covering of the full-level modular curve as the laws of its $\mathrm{Fin}$-indexed telescope: a dual-graph description of the special fibre with $N$ components and $M$ annuli, together with the genus relation, the disc-fibre property, the annulus widths and the partition of places. In this form it feeds the generic $\mathrm{Fin}$-indexed semistable-covering machinery used to construct the Tate-product maps on the Jacobian at level $q^2M'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_telescope_laws.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.telescope_laws
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (𝒞 : SemistableCovering q M' A W) (π : A) (hWd : 𝒞.WidthClause π)
    (hG : 𝒞.GenusClause) (hD : 𝒞.DiscFibreClause) (hC : 𝒞.CurveClause) :
      AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(fieldBar q M') + 𝒞.teleN =
        ∑ i : Fin 𝒞.teleN, AlgebraicCurve.genusFF (ResidueField ↥A) (𝒞.teleFbar i) + 𝒞.teleM + 1 ∧
      (∀ i, IsCurveOver (ResidueField ↥A) (𝒞.teleFbar i)) ∧ (∀ i, Algebra.EssFiniteType (ResidueField ↥A) (𝒞.teleFbar i)) ∧
      (∀ i, ∀ Q : Place (ResidueField ↥A) (𝒞.teleFbar i), Q ∉ (𝒞.teleChart i).nodes →
        ∃ (T : ↥(fieldBar q M')) (hT : T ∈ (𝒞.teleChart i).integers),
          (𝒞.teleChart i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((𝒞.teleChart i).residue ⟨T, hT⟩) = 1 ∧
          (∀ P ∈ (𝒞.teleChart i).dom, (𝒞.teleChart i).placeMap P = Q → T ∈ P.toValuationSubring ∧
            ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
          ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
            ∃! P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ (𝒞.teleChart i).dom ∧ (𝒞.teleChart i).placeMap P = Q ∧ P.evalAt T = c) ∧
      (∀ e, 1 ≤ 𝒞.teleWidth π e ∧ ∃ u : Aˣ, (𝒞.teleAn e).modulus = u * π ^ 𝒞.teleWidth π e) ∧
      (∀ i, HasPrincipalDivisors (ResidueField ↥A) (𝒞.teleFbar i)) ∧
      (∀ i (Q : Place (ResidueField ↥A) (𝒞.teleFbar i)), Q.IsRational) ∧
      (∀ e, (𝒞.teleAn' e).dom = (𝒞.teleAn e).dom ∧ (𝒞.teleAn' e).modulus = (𝒞.teleAn e).modulus ∧
        ((𝒞.teleAn e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (𝒞.teleAn' e).param * (𝒞.teleAn e).param
          = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((𝒞.teleAn e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (𝒞.teleAn e).IsAttached (𝒞.teleChart (𝒞.teleSrc e)) (𝒞.teleXs e) ∧ (𝒞.teleAn' e).IsAttached (𝒞.teleChart (𝒞.teleTgt e)) (𝒞.teleXt e)) ∧
      (∀ i, ∀ x ∈ (𝒞.teleChart i).nodes, ∃! e,
        (⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ : Σ j, Place (ResidueField ↥A) (𝒞.teleFbar j)) = ⟨i, x⟩ ∨
        (⟨𝒞.teleTgt e, 𝒞.teleXt e⟩ : Σ j, Place (ResidueField ↥A) (𝒞.teleFbar j)) = ⟨i, x⟩) ∧
      (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'),
        (∃ i, P ∈ (𝒞.teleChart i).dom ∧ (∀ j, P ∈ (𝒞.teleChart j).dom → j = i) ∧ ∀ e, P ∉ (𝒞.teleAn e).dom) ∨
        (∃ e, P ∈ (𝒞.teleAn e).dom ∧ (∀ e', P ∈ (𝒞.teleAn e').dom → e' = e) ∧ ∀ i, P ∉ (𝒞.teleChart i).dom)) := by sorry
