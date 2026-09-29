-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv
-- name    : ModularCurve.JHPlaceSpecialization.isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/2fc2c439-b03d-50e3-a2db-26b2a589afef
-- title:
--   Vanishing component map forces good classes at level Γ_H
-- statement:
--   Fix a prime $p$, a positive integer $M$ with $p \mid M$ and $M/p$ positive, and a subgroup $H \le (\mathbf{Z}/M)^\times$; let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ whose residue field $\kappa$ is algebraically closed of characteristic $p$, and write $F_M =$ `xHFunctionFieldBar M H`, $F_{M/p} =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` and $\bar F =$ `Fbar p M H hpM κ`. Let $\theta$ be a $\overline{\mathbf{Q}}$-algebra automorphism of $F_M$ and $\alpha : F_{M/p} \to F_M$ a $\overline{\mathbf{Q}}$-algebra map, with $\alpha$ and $\beta := \theta \circ \alpha$ integral; let $\delta$ be a self-map of the set of places of $\bar F$ over $\kappa$, and $SS$ a nonempty finite set of pairs of such places, each coordinate of each pair satisfying `Fixed`, i.e. carried back to itself by $\delta$ composed with the mod-$p$ $q$-expansion Frobenius on places. Let $Psp$ be a place specialisation datum `JHPlaceSpecialization p M H hpM A`, let $e : SS \to \mathbf{N}$ have all values positive, and put $m(e) = \sum_{s} \operatorname{lcm}(e)/e_s$. Let `comp` be an additive map from the inertia invariants of $J_H = \mathrm{Pic}^0(F_M)$ — the classes fixed by every element of the inertia subgroup of $A$ over $\mathbf{Q}$ — to the component group attached to $e$ (the dual of the character lattice of $SS$ modulo the image of the Gram map). The hypotheses are: (i) for every degree-zero divisor $D$ whose class lies in the inertia invariants and which is good for $(Psp,\alpha,\beta,\delta)$, meaning that each place in its support is strictly of the first or of the second kind, and every $s_0 \in SS$, one has $\mathrm{comp}[D] = \deg(\mathrm{sndDiv}\,D)\cdot \overline{e_{s_0}\,\mathrm{pr}_{s_0}}$, the image in the component group of $e_{s_0}$ times the $s_0$-coordinate functional restricted to the character lattice; (ii) there exists a principal good divisor $G$ with $\deg(\mathrm{fstDiv}\,G) = m(e)$ and $\deg(\mathrm{sndDiv}\,G) = -m(e)$; (iii) $x$ lies in the inertia invariants, admits a good degree-zero representative divisor, and $\mathrm{comp}\,x = 0$. The conclusion is that $x$ is a good class: there is a degree-zero divisor $D$, good for $(Psp,\alpha,\beta,\delta)$, with class $x$, whose gluing datum $(\mathrm{reduceFst}_*(\mathrm{fstDiv}\,D), \mathrm{reduceSnd}_*(\mathrm{sndDiv}\,D), 0)$ is admissible for $SS$, that is, both divisors have degree zero and vanish at the first, respectively second, coordinate of every pair in $SS$.
--
--   This is the component-group step in the analysis of the Néron model of $J_H$ at $p$ via place specialisations: a class in the inertia invariants that has a good representative and is killed by the component map can be corrected, using the principal good divisor of bidegree $(m(e), -m(e))$, to a representative whose gluing datum is admissible. It is one of the inputs to [`ModularCurve.JHPlaceSpecialization.exists_componentMap_gluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg`](thm.html#ModularCurve.JHPlaceSpecialization.exists_componentMap_gluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hfix : ∀ s ∈ SS, JHPlaceSpecialization.Fixed p M H hpM A δ s.1 ∧ JHPlaceSpecialization.Fixed p M H hpM A δ s.2)
    (hSS0 : SS.Nonempty)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (e : ↥SS → ℕ) (hpos : ∀ s, 0 < e s)
    (comp : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ componentGroup e)
    (hlaw : ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
        (hI : Pic0.mk D ∈ JHPlaceSpecialization.inertiaInvariants M H A),
        Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        ∀ s₀ : ↥SS,
          comp ⟨Pic0.mk D, hI⟩ =
            (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).degree •
              componentGroupProj e ((e s₀ : ℤ) • (LinearMap.proj s₀ : (↥SS → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ↥SS).subtype))
    (hG : ∃ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        Divisor.IsPrincipal G ∧ Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G ∧
          (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = ((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ) ∧
          (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = -((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ))
    (x : ↥(JHPlaceSpecialization.inertiaInvariants M H A))
    (hrep : ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧ Pic0.mk D = (x : JH M H))
    (hx : comp x = 0) :
    Psp.IsGoodClass α (θ.toAlgHom.comp α) hα hβ δ SS (x : JH M H) := by sorry
