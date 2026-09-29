-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_algebraMap_mem_of_le_igusaRing_descent_of_eq_two
-- name    : ModularCurve.FullLevel.algebraMap_mem_of_le_igusaRing_descent_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/1e6976e8-ab1c-5160-8c6a-fe0936eeb9d5
-- title:
--   Constants lie in any valuation ring below an Igusa ring (q=2)
-- statement:
--   Fix the prime $q$ with $q=2$, a level $M'\neq 0$ with $q\nmid M'$, and a valuation subring $A\subseteq\overline{\mathbb Q}$ with $q$ a non-unit of $A$. Let $W$ be a finite set of places of `modularFunctionFieldC (ResidueField A) M'` consisting exactly of the supersingular places (rational affine geometric places at which the generator $j$ takes a supersingular value), and assume $\overline{\mathbb Q}\cdot F(\Gamma(M'))=$ `modularFunctionFieldBar M'` is contained in $F=$ `fieldBar q M'`, the base change to $\overline{\mathbb Q}$ of the level-$H$ function field at level $q^2M'$. Further data: a constant reduction $R_0$ of `modularFunctionFieldBar M'` along $A$ compatible with coefficientwise reduction of Laurent series over $A$; an element $\pi\in A$ with $\pi^{q^2-1}=q$; an index $\zeta$ of primitive $q$-th roots of unity; families of valuation subrings $O_{\mathrm{Ig}}(\ell)$ of $F$ indexed by $\ell\in\mathbb P^1(\mathbb F_q)$ and $O_{\mathrm{SS}}(s)$ indexed by $s\in W$, subject to: the explicit description of $O_{\mathrm{Ig}}$ at the line at infinity by quotients of Laurent series over $A$ with non-vanishing reduced denominator, transitivity of the $\Gamma_0(M')$-level automorphisms `levelAutBar q M' ζ γ` on the $O_{\mathrm{Ig}}(\ell)$, injectivity of $O_{\mathrm{Ig}}$, permutation of the family by all level automorphisms, the constants of each $O_{\mathrm{SS}}(s)$ being exactly $A$, compatibility of $O_{\mathrm{SS}}(s)$ with $R_0$-residues and the place $s$ (including that $f-a$ lies in the maximal ideal when the residue of $a$ is the value of the $R_0$-residue of $f$ at $s$), invariance of each $O_{\mathrm{SS}}(s)$ under the level automorphisms, and the existence for each $s$ of $t\in O_{\mathrm{SS}}(s)$ with $t-a$ a unit for every $a\in A$; a subfield $K_0\subseteq\overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi\in K_0$; a henselian discrete valuation ring $A_0$ with an injective local ring homomorphism $\iota:A_0\to A$ whose image is $A\cap K_0$, with surjective induced residue map and uniformiser $\varpi_0$ satisfying $\iota(\varpi_0)=\pi$; the subfield $F_0\subseteq F$ of those elements all of whose Laurent coefficients lie in $K_0$, containing the image of $\hat\jmath$; and an $A_0$-algebra structure on $F_0$ whose structure map is $\iota$ followed by the inclusion of constants. The conclusion: for every $\ell\in\mathbb P^1(\mathbb F_q)$ and every valuation subring $V$ of $F_0$ all of whose elements lie in $O_{\mathrm{Ig}}(\ell)$, one has $a\in V$ for all $a\in A_0$, i.e. $V$ contains the constants $A_0$.
--
--   This is the statement that a valuation subring of the descended field $F_0$ lying below the traced Igusa ring $O_{\mathrm{Ig}}(\ell)\cap F_0$ automatically contains the ring of constants $A_0$, in the $q=2$ case of the Igusa-chart analysis of the geometric full-level modular function field. It is obtained from [`ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_two) and is used in the subsequent identification of valuation rings over the Igusa and Gauss rings in the construction of the semistable covering at $q=2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_algebraMap_mem_of_le_igusaRing_descent_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.algebraMap_mem_of_le_igusaRing_descent_of_eq_two
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
    (ℓ : CuspidalType.ProjLine q) (V : ValuationSubring ↥F₀)
    (hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg ℓ) :
    ∀ a : A₀, algebraMap A₀ ↥F₀ a ∈ V := by sorry
