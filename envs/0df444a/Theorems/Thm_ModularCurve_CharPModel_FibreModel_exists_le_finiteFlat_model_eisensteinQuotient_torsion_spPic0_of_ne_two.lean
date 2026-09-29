-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_exists_le_finiteFlat_model_eisensteinQuotient_torsion_spPic0_of_ne_two
-- name    : ModularCurve.CharPModel.FibreModel.exists_le_finiteFlat_model_eisensteinQuotient_torsion_spPic0_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/576b5261-3da4-58ca-b3fb-3464cfd5febc
-- title:
--   Finite flat model of Eisenstein quotient torsion along `spPic0`
-- statement:
--   Fix $p\ge 1$ with a Hecke action on $J_0(p)$ whose operators commute pairwise (`HeckeOperatorsCommuteBar p`), and a prime $\ell\neq 2$ with $\ell\nmid p$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$ and residue field of characteristic $\ell$, let `fm` be a `FibreModel` of level $p$ over $A$ with reduction the residue map, let `cc` be a cusp chart for `fm`, let `dataAll` assign to each divisor $d\mid p$ a modular polynomial datum, assume the reduction mod $\ell$ of $\Phi_p$ is separable over $\mathrm{RatFunc}$ of the residue field, and assume `fm.SpDivPreservesPrincipal`, i.e. the divisor specialisation sends degree-zero divisors to degree-zero divisors and principal ones to principal ones. Then for every $k$ there are $n\ge k$ and a commutative ring $H$ which is a finite flat cocommutative Hopf algebra over the subring $\mathbb{Z}_{(\ell)}\subset\mathbb Q$ of rationals with denominator coprime to $\ell$, together with a bijection $e$ from `WithConv` of the $\mathbb{Z}_{(\ell)}$-algebra maps $H\to\overline{\mathbb Q}$ onto the $\ell^n$-torsion of the Eisenstein quotient $J_0(p)/\mathrm{(Eisenstein\ kernel)}$, such that $e(fg)=e(f)+e(g)$; $e$ is Galois equivariant in the sense that if $g=\sigma\circ f$ and $x\in J_0(p)$ has class $e(f)$, then $\sigma\cdot x$ has class $e(g)$; and for each $f$ with $\ell^k\cdot e(f)=0$ such that every lift $x$ of $e(f)$ satisfies $\mathrm{spPic0}(x)\in\mathrm{spKernelImage}$ (the image under `fm.spPic0` of the Eisenstein kernel submodule), one has $A$-valuation of $f(h)-\varepsilon(h)$ less than $1$ for all $h\in H$, where $\varepsilon$ is the counit.
--
--   This is the two-exponent form of the finite flat model statement for the $\ell$-power torsion of the Eisenstein quotient of $J_0(p)$, with the reduction clause phrased through the specialisation map `spPic0` built from a fibre model of $X_0(p)$ at $A$ rather than through the canonical reduction map. It feeds [`ModularCurve.exists_jZeroGoodReductionSpecialization_doorPredicates`](thm.html#ModularCurve.exists_jZeroGoodReductionSpecialization_doorPredicates), which packages the inputs needed for the Raynaud-type injectivity argument on the Eisenstein quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_exists_le_finiteFlat_model_eisensteinQuotient_torsion_spPic0_of_ne_two.lean

import Mathlib
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_StepThreeDoorPredicates
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel AlgebraicCurve IsLocalRing
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.CharPModel.FibreModel.exists_le_finiteFlat_model_eisensteinQuotient_torsion_spPic0_of_ne_two
    (p : ℕ) [NeZero p] (hcomm : HeckeOperatorsCommuteBar p)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p) (hℓ2 : ℓ ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ]
    (fm : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ p → ModularPolynomialData d)
    (hsep : (((dataAll p (dvd_refl p)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
      (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
    (hpres : fm.SpDivPreservesPrincipal Ideal.Quotient.mk_surjective dataAll hsep)
    (k : ℕ) :
    letI := heckeModuleBar p
    ∃ n : ℕ, k ≤ n ∧
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) H),
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) H ∧ Module.Flat (GaloisRep.ratLocalizedAt ℓ) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (EisensteinQuotient p (heckeModuleBar p)) ((ℓ : ℤ) ^ n)),
        (∀ f g, e (f * g) = e f + e g) ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
            (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) →
          ∀ x : JZero p, eisensteinQuotientMk p (heckeModuleBar p) x
              = (e f : EisensteinQuotient p (heckeModuleBar p)) →
            eisensteinQuotientMk p (heckeModuleBar p) (σ • x)
              = (e g : EisensteinQuotient p (heckeModuleBar p))) ∧
        (∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ),
          ((ℓ : ℤ) ^ k) • (e f : EisensteinQuotient p (heckeModuleBar p)) = 0 →
          (∀ x : JZero p, eisensteinQuotientMk p (heckeModuleBar p) x
              = (e f : EisensteinQuotient p (heckeModuleBar p)) →
            fm.spPic0 Ideal.Quotient.mk_surjective dataAll hsep x ∈
              spKernelImage (fm.spPic0 Ideal.Quotient.mk_surjective dataAll hsep)) →
          ∀ h : H, A.valuation (f h - algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)
            (Coalgebra.counit h)) < 1) := by sorry
