-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mem_maximalIdeal_drinfeldRing_of_mem_nonunits_igusaRing_chartAlgFin_descent_of_eq_two
-- name    : ModularCurve.FullLevel.mem_maximalIdeal_drinfeldRing_of_mem_nonunits_igusaRing_chartAlgFin_descent_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/ec292d21-676c-51c7-a6aa-d34881561175
-- title:
--   Igusa components pass through every Drinfeld point, q=2
-- statement:
--   Fix a prime $q$ with $q=2$ and a level $M'\ge 1$ with $q\nmid M'$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, and a finite set $W$ consisting exactly of the supersingular places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ (rational affine geometric places whose value at the geometric $j$ lies in the supersingular set). Assume $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$ via `hle`, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ with values in that reduced function field, compatible with coefficientwise reduction of Laurent series with coefficients in $A$ (`hR₀`). Further data: $\pi\in A$ with $\pi^{q^2-1}=q$; a primitive $q$-th root of unity $\zeta$; families $O_{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb Z/q)$ and $O_{\mathrm{SS}}$ indexed by $W$, subject to: $O_{\mathrm{Ig}}(\infty)$ consists of the quotients $x/y$ of coefficientwise images of Laurent series over $A$ with $y$ of non-zero reduction; each $O_{\mathrm{Ig}}(\ell)$ is the pullback of $O_{\mathrm{Ig}}(\infty)$ along some $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ with $\gamma\in\Gamma_0(M')$ moving $\infty$ to $\ell$; $O_{\mathrm{Ig}}$ injective; the level automorphisms $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$, $\gamma\in\Gamma_0(M')$, permute the $O_{\mathrm{Ig}}(\ell)$; $O_{\mathrm{SS}}(s)$ meets $\overline{\mathbb Q}$ exactly in $A$, is fixed by all those level automorphisms, contains an element $t$ with $t-a$ a unit for every $a\in A$, and receives every $f\in R_0$-integer which is regular wherever $\hat\jmath$ is and whose $R_0$-residue is in the valuation ring of $s$, with $f-a$ in the maximal ideal of $O_{\mathrm{SS}}(s)$ whenever the residue of $a\in A$ is the value of that residue at $s$. Finally let $K_0\subseteq\overline{\mathbb Q}$ be a subfield with $\overline{\mathbb Q}$ algebraic over it and $\pi\in K_0$, $A_0$ a henselian discrete valuation domain with an injective local homomorphism $\iota:A_0\to A$ whose image is $A\cap K_0$, inducing a surjection onto $\mathrm{ResidueField}\,A$, with $\mathfrak m_{A_0}=(\varpi_0)$ and $\iota\varpi_0=\pi$; let $F_0$ be the subfield of $\mathrm{fieldBar}\,q\,M'$ of those elements all of whose Laurent coefficients lie in $K_0$, containing the image $\hat\jmath$ of the $q$-expansion of $j$, with $\hat\jmath\neq 0$ and an $A_0$-algebra structure on $F_0$ compatible with $\iota$. Then for every $s\in W$, every $\ell\in\mathbb P^1(\mathbb Z/q)$ and every $g$ in $\mathrm{chartAlgFin}\,A_0\,F_0\,\hat\jmath$, the $A_0$-algebra of elements of $F_0$ integral over $A_0[\hat\jmath]$, whose image in $\mathrm{fieldBar}\,q\,M'$ is a non-unit of $O_{\mathrm{Ig}}(\ell)$, that image lies in $O_{\mathrm{SS}}(s)$ and in fact in the maximal ideal of $O_{\mathrm{SS}}(s)$.
--
--   Geometrically this says that on the descended two-chart integral model the finite (Igusa) chart sees each Igusa component $\ell$ passing through the contracted Drinfeld point attached to each supersingular place $s$: the ideal cut out by $\ell$ on the chart algebra is contained in the maximal ideal of the Drinfeld valuation ring at $s$. It is the $q=2$ case, where the Igusa covering of the $\infty$-branch is trivial, and it feeds the uniqueness statement [`ModularCurve.FullLevel.exists_isMaximal_mem_iff_mem_maximalIdeal_drinfeldRing_unique_chartAlgFin_descent_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_isMaximal_mem_iff_mem_maximalIdeal_drinfeldRing_unique_chartAlgFin_descent_of_eq_two) in the construction of the semistable covering of the full-level modular curve at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mem_maximalIdeal_drinfeldRing_of_mem_nonunits_igusaRing_chartAlgFin_descent_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.mem_maximalIdeal_drinfeldRing_of_mem_nonunits_igusaRing_chartAlgFin_descent_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ))
    [Fact ((⟨_, hjF₀⟩ : ↥F₀) ≠ 0)]
    (s : ↥W) (ℓ : CuspidalType.ProjLine q)
    (g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) (hg : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits) :
    ∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s) := by sorry
