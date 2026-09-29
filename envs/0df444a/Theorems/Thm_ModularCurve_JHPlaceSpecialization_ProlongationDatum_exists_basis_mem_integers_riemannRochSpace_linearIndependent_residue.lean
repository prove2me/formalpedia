-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_basis_mem_integers_riemannRochSpace_linearIndependent_residue
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_basis_mem_integers_riemannRochSpace_linearIndependent_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/889e6728-fa51-5edb-8aa2-e5496330ec47
-- title:
--   Bi-integral basis of a Riemann–Roch space with independent residues
-- statement:
--   Fix a prime $p$ and a level $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that maps to $1$ in $(\mathbb{Z}/(M/p))^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ whose residue field $\kappa$ is algebraically closed of characteristic $p$. Write $F_M$ for `xHFunctionFieldBar M H`, $F_{M/p}$ for the corresponding field at level $M/p$ and subgroup `infSubgroup p M H hpM`, and $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM κ`. The data are: a $\overline{\mathbb{Q}}$-automorphism $\theta$ of $F_M$ commuting with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on Laurent coefficients; integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$ acting on $q$-expansions by the identity and by $q \mapsto q^p$ respectively, with $\beta = \alpha$ followed by $\theta$; a unit $pb$ of $\mathbb{Z}/(M/p)$ equal to $p$; the map $\delta$ on places of $\bar F$ given by the action of the reduced diamond automorphism attached to [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36), assumed to have finite fixed-place set; a finset $SS$ whose members are exactly the pairs $(\mathrm{Frob}(v), v)$ with $v$ supersingular; a place specialization `Psp` and a prolongation datum `Rpd` for it relative to $\theta$, consisting of regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residues in $\bar F$, subject to the type dichotomy, the model laws (the two divisor laws and the two cusp laws), the order law at fixed affine places, and the regularity and node-value laws for $SS$. Then for every divisor $E$ on $F_M$ with finite-dimensional Riemann–Roch space $L(E) = \{f : v(f) \le \exp(E v)$ for all places $v\}$, there is a family $u$ indexed by $\mathrm{Fin}\,\dim_{\overline{\mathbb{Q}}} L(E)$ of elements of $F_M$, each lying in the integers of $R_1$ and of $R_2$ and in $L(E)$, such that the family of residue pairs $a \mapsto (R_1\text{-residue of } u_a,\ R_2\text{-residue of } u_a) \in \bar F \times \bar F$ is linearly independent over $\kappa$. The conclusion asserts the cardinality, membership in $L(E)$ and the independence of the residue pairs; it does not separately record that $u$ is a basis of $L(E)$.
--
--   This is the lattice step in Deuring's reduction of linear systems, adapted to the function field of $X_H(M)$ at a place above $p$ with $p \parallel M$: it produces a basis of a Riemann–Roch space simultaneously integral for both prolongations of the datum, with residue pairs spanning a $\kappa$-space of the full dimension. It feeds the common-unit constructions that exhibit elements with prescribed poles at fixed affine places and along the two reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_basis_mem_integers_riemannRochSpace_linearIndependent_residue.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Classical
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_basis_mem_integers_riemannRochSpace_linearIndependent_residue
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hFix : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace E)] :
    ∃ (u : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → ↥(xHFunctionFieldBar M H))
      (hu₁ : ∀ a, u a ∈ Rpd.R₁.integers) (hu₂ : ∀ a, u a ∈ Rpd.R₂.integers),
      (∀ a, u a ∈ riemannRochSpace E) ∧
      LinearIndependent (ResidueField ↥A) (fun a => ((Rpd.R₁.residue ⟨u a, hu₁ a⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))), (Rpd.R₂.residue ⟨u a, hu₂ a⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) := by sorry
