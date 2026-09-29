-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_algebraMap_mem_of_le_igusaRing_descent_of_eq_three
-- name    : ModularCurve.FullLevel.algebraMap_mem_of_le_igusaRing_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/21786653-8a41-5946-b502-58d1f724d0d2
-- title:
--   Constants lie in valuation subrings of the Igusa ring, q=3
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $q$ is a non-unit. Let $W$ be a finite set of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$, assumed to consist exactly of the supersingular places, i.e. the rational affine geometric places at which `jGeomGen` takes a value in `ssJSet q`. Assume `modularFunctionFieldBar M'`, the base change to $\overline{\mathbb Q}$ of the full level-$M'$ modular function field, is contained in `fieldBar q M'`, and let $R_0$ be a `ConstantReduction` of `modularFunctionFieldBar M'` along $A$ with values in `modularFunctionFieldC (ResidueField A) M'`, compatible with coefficientwise reduction in the sense that each Laurent series $y$ over $A$ lying in `modularFunctionFieldBar M'` belongs to $R_0$`.integers` and has $R_0$-residue the coefficientwise reduction of $y$. Fix $\pi \in A$ with $\pi^{q^2-1}=q$, a primitive $q$-th root of unity $\zeta$ (an element of `Idx q`), and families $\mathcal O_{\mathrm{Ig}}$ of valuation subrings of `fieldBar q M'` indexed by $\mathbb P^1(\mathbb F_q)$ and $\mathcal O_{\mathrm{SS}}$ indexed by $W$, subject to the following, summarised here: on the Igusa side, that $\mathcal O_{\mathrm{Ig}}$ at `lineInfty q` consists of the quotients $x/y$ of Laurent series with coefficients in $A$ whose denominator has nonzero reduction, that every line is reached from `lineInfty q` by some $\gamma \in \Gamma_0(M')$ via `redQ q` with $\mathcal O_{\mathrm{Ig}}$ at that line the pullback of $\mathcal O_{\mathrm{Ig}}(\mathrm{lineInfty})$ along `levelAutBar q M' ζ γ`, that $\mathcal O_{\mathrm{Ig}}$ is injective, and that the maps `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$ permute the family; on the supersingular side, that $\mathcal O_{\mathrm{SS}}\,s$ meets the constants exactly in $A$, that an $f \in R_0$`.integers` which is regular at every place of `modularFunctionFieldBar M'` where `coeffEmb` of `jq` is regular and whose $R_0$-residue lies in the valuation ring of $s$ has image in $\mathcal O_{\mathrm{SS}}\,s$, with $f-a$ in the maximal ideal for every $a \in A$ whose residue is the value at $s$ of that $R_0$-residue, that each $\mathcal O_{\mathrm{SS}}\,s$ is invariant under all `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$, and that each $\mathcal O_{\mathrm{SS}}\,s$ contains an element $t$ with $t-a$ a unit for every $a \in A$. Let $K_0 \subseteq \overline{\mathbb Q}$ be a subfield with $\overline{\mathbb Q}$ algebraic over it and $\pi \in K_0$, and let $A_0$ be a Henselian discrete valuation domain with an injective local ring map $\iota$ into $A$ whose image in $\overline{\mathbb Q}$ is exactly $A \cap K_0$, inducing a surjection onto the residue field of $A$ and sending a generator $\varpi_0$ of the maximal ideal to $\pi$. Let $F_0$ be the subfield of `fieldBar q M'` of elements all of whose Laurent coefficients lie in $K_0$; it contains the image of `coeffEmb` of `jq`, and carries an $A_0$-algebra structure whose structure map is $\iota$ followed by $\overline{\mathbb Q} \to$ `fieldBar q M'`. Then for every line $\ell$ and every valuation subring $V$ of $F_0$ all of whose elements map into $\mathcal O_{\mathrm{Ig}}\,\ell$, every element $\mathrm{algebraMap}\,A_0\,F_0\,a$, $a \in A_0$, lies in $V$.
--
--   This is the $q=3$ case of the statement that a valuation subring of the descended field $F_0$ lying inside the traced Igusa ring automatically contains the ring of constants $A_0$, a rigidity step in the construction of the semistable covering of the full-level modular curve along its Igusa charts. It rests on the identification of the Igusa ring with a Gauss-type ring, and is used in the three subsequent descent results on the Igusa leg of that construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_algebraMap_mem_of_le_igusaRing_descent_of_eq_three.lean

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

theorem ModularCurve.FullLevel.algebraMap_mem_of_le_igusaRing_descent_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
