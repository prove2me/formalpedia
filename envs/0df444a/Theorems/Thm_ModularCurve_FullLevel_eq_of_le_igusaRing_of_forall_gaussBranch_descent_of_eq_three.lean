-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_eq_of_le_igusaRing_of_forall_gaussBranch_descent_of_eq_three
-- name    : ModularCurve.FullLevel.eq_of_le_igusaRing_of_forall_gaussBranch_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/1cc6fdae-4600-5285-b4ec-0326d24411dc
-- title:
--   Level transport of Igusa-branch uniqueness at q = 3
-- statement:
--   Fix a prime $q$ with $q = 3$, a level $M'$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ in its nonunits. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over $\mathrm{ResidueField}\,A$ consisting exactly of the supersingular places (rational, affine geometric, with $\mathrm{jGeomGen}$ evaluating into $\mathrm{ssJSet}\,q$). Assume $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$, and let $R_0$ be a constant reduction of the former along $A$ onto that residue function field, whose residue map agrees with coefficientwise reduction of Laurent series over $A$. Let $\pi \in \overline{\mathbb{Q}}$ satisfy $\pi^{q^2-1} = q$ and $\pi \in A$, let $\zeta$ be a primitive $q$-th root of unity, and let $O_{\mathrm{Ig}}$ index valuation subrings of $\mathrm{fieldBar}\,q\,M'$ by $\mathbb{P}^1(\mathbb{Z}/q)$, $O_{\mathrm{SS}}$ index such subrings by $W$. The hypotheses on these data are: $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ consists of those $f$ admitting Laurent series $x, y$ over $A$ with $y$ having nonzero coefficientwise reduction and $f\,y = x$; each $O_{\mathrm{Ig}}(\ell)$ is the pullback of $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ for some $\gamma \in \Gamma_0(M')$ with $\mathrm{redQ}\,q\,\gamma \cdot \mathrm{lineInfty}\,q = \ell$; $O_{\mathrm{Ig}}$ is injective and its family is permuted by pullback along every $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$; each $O_{\mathrm{SS}}(s)$ meets $\overline{\mathbb{Q}}$ in $A$, is invariant under those same automorphisms, contains an element $t$ with $t - a$ a unit for all $a \in A$, and is compatible with $R_0$ in the sense that an element $f$ of $R_0.\mathrm{integers}$ which has nonnegative order at every place where the modular invariant $\mathrm{jq}$ does, and whose $R_0$-residue lies in the valuation subring of $s$, has image in $O_{\mathrm{SS}}(s)$, with $f - a$ in the maximal ideal whenever the residue of $a \in A$ is the value of the $R_0$-residue of $f$ at $s$. Descent data: a subfield $K_0 \subseteq \overline{\mathbb{Q}}$ with $\overline{\mathbb{Q}}$ algebraic over it and $\pi \in K_0$; a henselian discrete valuation domain $A_0$ with an injective local homomorphism $\iota : A_0 \to A$ whose image is $A \cap K_0$, with $\mathrm{residue} \circ \iota$ surjective, and with a generator $\varpi_0$ of the maximal ideal satisfying $\iota(\varpi_0) = \pi$; the subfield $F_0$ of $\mathrm{fieldBar}\,q\,M'$ of elements all of whose Laurent coefficients lie in $K_0$, which contains the image $\hat{\jmath}$ of $\mathrm{jq}$, together with an $A_0$-algebra structure on $F_0$ induced by $\iota$. Finally assume, for the line at infinity: for all $s \in W$ and valuation subrings $V, V'$ of $F_0$ both mapping into $O_{\mathrm{Ig}}(\mathrm{lineInfty}\,q)$, both failing to contain some element of $F_0$ whose image lies there, and both having as nonunits every $g \in F_0$ integral over $A_0[\hat{\jmath}]$ whose image lies in the maximal ideal of $O_{\mathrm{SS}}(s)$, one has $V = V'$. The conclusion is the identical assertion with $\mathrm{lineInfty}\,q$ replaced by an arbitrary $\ell \in \mathbb{P}^1(\mathbb{Z}/q)$.
--
--   This is the level-transport step on the Igusa leg of the construction of semistable coverings of modular curves: uniqueness of a proper refinement of the Igusa valuation ring over a fixed supersingular place, known for the branch at infinity, is propagated to all branches by the action of $\Gamma_0(M')$ through the level automorphisms $\mathrm{levelAutBar}$. It is the $q = 3$ case, and is used by [`ModularCurve.FullLevel.eq_of_le_igusaRing_of_forall_isIntegral_mem_maximalIdeal_drinfeldRing_mem_nonunits_descent_of_eq_three`](thm.html#ModularCurve.FullLevel.eq_of_le_igusaRing_of_forall_isIntegral_mem_maximalIdeal_drinfeldRing_mem_nonunits_descent_of_eq_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_eq_of_le_igusaRing_of_forall_gaussBranch_descent_of_eq_three.lean

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

theorem ModularCurve.FullLevel.eq_of_le_igusaRing_of_forall_gaussBranch_descent_of_eq_three
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
    (hinf : ∀ (s : ↥W) (V V' : ValuationSubring ↥F₀),
        (∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q)) →
        (∀ f : ↥F₀, f ∈ V' → (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q)) →
        (∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ∧ f ∉ V) →
        (∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ∧ f ∉ V') →
        (∀ g : ↥F₀, _root_.IsIntegral ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) g →
          (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) →
            g ∈ V.nonunits) →
        (∀ g : ↥F₀, _root_.IsIntegral ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) g →
          (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) →
            g ∈ V'.nonunits) →
        V = V') :
    ∀ (ℓ : CuspidalType.ProjLine q), ∀ (s : ↥W) (V V' : ValuationSubring ↥F₀),
        (∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg ℓ) →
        (∀ f : ↥F₀, f ∈ V' → (f : ↥(fieldBar q M')) ∈ OIg ℓ) →
        (∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg ℓ ∧ f ∉ V) →
        (∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg ℓ ∧ f ∉ V') →
        (∀ g : ↥F₀, _root_.IsIntegral ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) g →
          (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) →
            g ∈ V.nonunits) →
        (∀ g : ↥F₀, _root_.IsIntegral ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) g →
          (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) →
            g ∈ V'.nonunits) →
        V = V' := by sorry
