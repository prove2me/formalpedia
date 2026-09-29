-- Prove2me | Theorems.Thm_ModularCurve_exists_le_finiteFlat_model_eisensteinQuotient_torsion_reductionModL_of_ne_two
-- name    : ModularCurve.exists_le_finiteFlat_model_eisensteinQuotient_torsion_reductionModL_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/1e7c68c4-c645-5317-b96e-eb6141ac4b50
-- title:
--   Two-exponent finite flat model of Eisenstein quotient torsion
-- statement:
--   Fix $p \ge 1$ and assume `HeckeOperatorsCommuteBar p`, i.e. the operators `heckeOperatorBar p ℓ'` commute pairwise as endomorphisms of $J =$ `JZero p`, the degree-zero divisor class group $\mathrm{Pic}^0$ of the modular function field of level $p$ over $\overline{\mathbb{Q}}$; $J$ then carries the Hecke-algebra module structure `heckeModuleBar p`, with `HeckeAlg` $= \mathbb{Z}[T_{\ell'} : \ell' \text{ prime}]$. Let $\ell \neq 2$ be a prime with $\ell \nmid p$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$ and residue field of characteristic $\ell$, assume the reduction data `ReductionInputsModL A p` for the residue map of $A$ at level $p$, and let $k \in \mathbb{N}$. Then there is $n \ge k$ and a type $H$ carrying a commutative ring structure and a Hopf-algebra structure over the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) $\subset \mathbb{Q}$ of rationals whose denominator is coprime to $\ell$, module-finite, flat and cocommutative over that subring, together with a bijection $e$ from `WithConv` of the algebra maps $H \to \overline{\mathbb{Q}}$ onto the $\ell^n$-torsion `Submodule.torsionBy ℤ` of the Eisenstein quotient `EisensteinQuotient p` $= J /$ `eisensteinKernelSubmodule`, such that: (i) $e(f \cdot g) = e(f) + e(g)$; (ii) for $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and $f, g$ with $g(h) = \sigma(f(h))$ for all $h \in H$, whenever $x \in J$ has image $e(f)$ under `eisensteinQuotientMk`, the image of $\sigma \cdot x$ is $e(g)$; (iii) for every $f$ with $\ell^k \cdot e(f) = 0$ such that every $x \in J$ lifting $e(f)$ satisfies `reductionModL A p x` $\in$ `spKernelImage (reductionModL A p)`, the image of the Eisenstein kernel submodule under the reduction map, one has $A$-valuation of $f(h) - \varepsilon(h)$ (the counit of $h$, mapped into $\overline{\mathbb{Q}}$) strictly less than $1$ for all $h \in H$.
--
--   This is the two-exponent form of the finite flat group-scheme model, over the localisation of $\mathbb{Z}$ at $\ell$, of the $\ell$-power torsion of the Eisenstein quotient of $J_0(p)$: the model is produced at an exponent $n \ge k$, while the compatibility with reduction at a place above $\ell$ is asserted only for classes killed by $\ell^k$. It feeds the corresponding statement about the special fibre, [`ModularCurve.CharPModel.FibreModel.exists_le_finiteFlat_model_eisensteinQuotient_torsion_spPic0_of_ne_two`](thm.html#ModularCurve.CharPModel.FibreModel.exists_le_finiteFlat_model_eisensteinQuotient_torsion_spPic0_of_ne_two), in the analysis of rational points on $X_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_le_finiteFlat_model_eisensteinQuotient_torsion_reductionModL_of_ne_two.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_StepThreeDoorPredicates
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve IsLocalRing
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_le_finiteFlat_model_eisensteinQuotient_torsion_reductionModL_of_ne_two
    (p : ℕ) [NeZero p] (hcomm : HeckeOperatorsCommuteBar p)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p) (hℓ2 : ℓ ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ]
    (hinp : ReductionInputsModL A p)
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
            reductionModL A p x ∈
              spKernelImage (reductionModL A p)) →
          ∀ h : H, A.valuation (f h - algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)
            (Coalgebra.counit h)) < 1) := by sorry
