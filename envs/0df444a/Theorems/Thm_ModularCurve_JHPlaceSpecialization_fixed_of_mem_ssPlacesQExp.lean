-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_fixed_of_mem_ssPlacesQExp
-- name    : ModularCurve.JHPlaceSpecialization.fixed_of_mem_ssPlacesQExp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/e5f9d59d-e539-594a-87bf-1dc9877192d5
-- title:
--   Supersingular places are fixed by Frobenius–diamond–Frobenius
-- statement:
--   Fix a prime $p$ and a natural number $M \neq 0$ with $p \mid M$ but $p^2 \nmid M$ (so $M/p \neq 0$), and a subgroup $H \le (\mathbb{Z}/M)^\times$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed, and write $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field $\kappa \cdot F(\Gamma')$ attached to the group `ΓN p M H hpM`. Let $\bar p \in (\mathbb{Z}/(M/p))^\times$ be a unit whose underlying residue equals $p$ in $\mathbb{Z}/(M/p)$. Let $\delta$ be a self-map of the set of places `Place κ F̄` which is assumed to act as the semilinear automorphism `SemilinearAut.ofAlgAut` of the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) p̄)`, where `infSubgroup p M H hpM` is the image of $H$ under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ and [`CuspForm.gammaLift`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) chooses a lift of $\bar p$ to $\Gamma_0(M/p)$. Then for every place $y$ lying in `ssPlacesQExp κ (ΓN p M H hpM) p`, i.e. every place satisfying the supersingularity predicate `IsSSPlaceQExp`, the conclusion `JHPlaceSpecialization.Fixed δ y` holds: applying the place-level Frobenius `qExpFrobeniusPlaceModL κ Γ′ p`, then $\delta$, then `qExpFrobeniusPlaceModL κ Γ′ p` again, returns $y$.
--
--   This is the place-theoretic form of the relation $\mathrm{Frob}^2 = \langle p \rangle^{-1}$ on the supersingular points of the mod-$p$ reduction of a modular curve of level $\Gamma_H$ with $p \parallel M$, phrased for the abstract $q$-expansion function field rather than for a chosen model. It supplies the hypothesis `Fixed` demanded by the divisor and regularity laws of the place-specialisation data for $J_H(M)$ at $p$, and is used by the model and prolongation lemmas for that data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_fixed_of_mem_ssPlacesQExp.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.JHNeronObjectAtP
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.fixed_of_mem_ssPlacesQExp
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) →
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (y : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hy : y ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) :
    JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ y := by sorry
