-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_supersingularDVR_residuallyTranscendental_of_affineChart_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.supersingularDVR_residuallyTranscendental_of_affineChart_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/7e0b362f-01d3-5137-8fad-d93a2415cc82
-- title:
--   Residual transcendence of the supersingular chart valuation ring (q=3)
-- statement:
--   Fix a prime $q$ with $q=3$, an integer $M'\ge 1$ with $q\nmid M'$, and a prime $\ell_g$ with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}(\mathrm{ResidueField}\,A,M')$ consisting exactly of the supersingular places (rational, lying on the affine geometric locus, with $j$-value in $\mathrm{ssJSet}$), assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with values in that function field, whose residue map is computed coefficientwise on Laurent series with coefficients in $A$; fix $s\in W$. Further data: a subfield $k_0\subseteq\overline{\mathbb{Q}}$ and $\pi_0\in k_0\cap A$ such that $A\cap k_0$ is a henselian discrete valuation ring with maximal ideal $(\pi_0)$ and algebraically closed residue field, every element of $A$ being congruent modulo the maximal ideal of $A$ to an element of $k_0\cap A$; a prime $\ell\ge 3$ with $\ell\ne q$, $\ell\nmid M'$; an element $\zeta_0\in k_0$ which is a primitive $q\ell$-th root of unity; and $\varpi_t\in k_0\cap A$ with $\varpi_t^{q^2-1}=q u$ for some unit $u$ of $A$. Finally, $K_b$ is the trivial $k_0$-subextension of $\overline{\mathbb{Q}}$, $A_b$ the valuation subring of $K_b$ cut out by $A$, and $\varpi_b\neq 0$ a generator of its maximal ideal. The conclusion, for the $k_0$-algebra structure on $\mathrm{fieldBar}\,q\,M'$ obtained by composition, asserts: let $F_0$ be an intermediate field of $\mathrm{fieldBar}\,q\,M'$ over $k_0$ and $W_0$ a valuation subring of $F_0$ inducing $A$ on $k_0$; let $B$ be a subring of $\mathrm{fieldBar}\,q\,M'$ with an $A_b$-algebra structure compatible with the inclusions into $\mathrm{fieldBar}\,q\,M'$, such that $B\subseteq W_0$, the image of $\varpi_b$ is prime in $B$, and $W_0$ consists exactly of the ratios $g/h$ with $g,h\in B$ and $\varpi_b\nmid h$; assume moreover that for every $\mathbb{F}_{q^2}$-algebra structure on $\mathrm{ResidueField}\,A$, every proof that $\mathrm{CoordRing}\,q\,(\mathrm{ResidueField}\,A)$ is a domain and every primitive $q$-th root of unity $\zeta$ in $\overline{\mathbb{Q}}$, there are a subgroup $C_s$ of the $(q+1)$-st roots of unity of $\mathbb{F}_{q^2}$ and a ring homomorphism $\rho$ from $B$ to the fixed field $\mathrm{quotField}\,q\,(\mathrm{ResidueField}\,A)\,C_s$ inside the Drinfeld function field with: $\#C_s=2\,\mathrm{placeWidthChar}\,q\,M'\,s$; $\ker\rho=(\varpi_b)$; $\rho$ restricting on $A_b$ to the residue map of $A$; every element of the target a ratio $\rho(g)/\rho(h)$; the image of $\rho$ being exactly the part of the target lying in the image of the Drinfeld coordinate ring; and $\rho$ intertwining the level automorphisms $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma^{-1}$, for $\gamma\in\Gamma_0(M')$ whose reduction lies in $\mathrm{hSubgroup}$, with $\mathrm{hFunctionFieldAction}$. Then there exists $t\in W_0$ such that for every polynomial $p$ over $k_0$ all of whose coefficients lie in $A$, if $p(t)$ lies in the maximal ideal of $W_0$ then every coefficient of $p$ lies in the maximal ideal of $W_0$; that is, the residue of $t$ is transcendental over the residue field of $A$.
--
--   This is the residual transcendence (in Deuring's terminology, a prime divisor of the first kind) of the valuation ring attached to a supersingular place, read off from the affine Drinfeld chart: the specialisation $\rho$ of $B$ onto the Drinfeld quotient curve over the residue field forces the residue field of $W_0$ to contain a transcendental element. It is the $q=3$ instance, under the auxiliary level guard provided by a prime $\ell_g\equiv 11 \pmod{12}$ dividing $M'$, and it feeds the construction of the semistable chart at supersingular places through [`ModularCurve.FullLevel.exists_klevel_supersingularDVR_affineChart_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.exists_klevel_supersingularDVR_affineChart_of_eq_three_of_dvd) and [`ModularCurve.FullLevel.klevel_supersingularDVR_affineChart_of_levelField_affineChart_of_eq_three_of_dvd`](thm.html#ModularCurve.FullLevel.klevel_supersingularDVR_affineChart_of_levelField_affineChart_of_eq_three_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_supersingularDVR_residuallyTranscendental_of_affineChart_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.supersingularDVR_residuallyTranscendental_of_affineChart_of_eq_three_of_dvd
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKb : Kb = ⊥)
    (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (ϖb : ↥Ab) (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb}) (hϖb0 : ϖb ≠ 0) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')) (W₀ : ValuationSubring ↥F₀),

      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) →
    ∀ (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B),

        (∀ a : ↥Ab, ((@algebraMap ↥Ab ↥B _ _ alg a : ↥B) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) →

        (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ W₀) →
        Prime (@algebraMap ↥Ab ↥B _ _ alg ϖb) →
        (∀ f : ↥F₀, f ∈ W₀ ↔ ∃ g h : ↥B, ¬ (@algebraMap ↥Ab ↥B _ _ alg ϖb ∣ h) ∧ (f : ↥(fieldBar q M')) * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) →

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (ρ : ↥B →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            RingHom.ker ρ = Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb} ∧
            (∀ a : ↥Ab, ρ (@algebraMap ↥Ab ↥B _ _ alg a) =
              algebraMap (ResidueField ↥A) ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) (IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩)) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), ∃ g h : ↥B, ρ h ≠ 0 ∧ z * ρ h = ρ g) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), z ∈ Set.range ρ ↔
              (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈ Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q)
                (f : ↥B) (hf' : levelAutBar q M' ζ γ⁻¹ (f : ↥(fieldBar q M')) ∈ B),
                ((ρ ⟨_, hf'⟩ : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                  DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((ρ f : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) →

      (∃ t : ↥W₀, ∀ p : Polynomial ↥k₀, (∀ n, ((p.coeff n : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
        (∃ hm : Polynomial.aeval (t : ↥F₀) p ∈ W₀, (⟨_, hm⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) →
          ∀ n, ∃ hc : algebraMap ↥k₀ ↥F₀ (p.coeff n) ∈ W₀, (⟨_, hc⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) := by sorry
