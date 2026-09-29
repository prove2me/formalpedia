-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_three
-- name    : ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/bd036916-0668-5d11-a4a5-e8774093a88d
-- title:
--   Gauss-component chart dichotomy for the descended model, q=3
-- statement:
--   Fix a prime $q$ with $q=3$, a level $M'\neq 0$ with $q\nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$. Let $W$ be the finite set of places $w$ of $\mathrm{modularFunctionFieldC}$ over $\mathrm{ResidueField}\,A$ that are exactly the supersingular ones (rational, affine geometric, with $w$-value of the geometric $j$-generator in $\mathrm{ssJSet}$), let $\mathrm{modularFunctionFieldBar}\,M'\le \mathrm{fieldBar}\,q\,M'$ via `hle`, and let $R_0$ be a constant reduction of the former over $A$ with residue field the former's reduction, compatible coefficientwise with reduction of Laurent series over $A$ (`hR₀`). Assume $\pi\in A$ with $\pi^{q^2-1}=q$, a primitive $q$-th root of unity $\zeta$, and families $\mathcal O_{\mathrm{Ig}}$ indexed by $\mathbb P^1(\mathbb F_q)$ and $\mathcal O_{\mathrm{ss}}$ indexed by $W$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ subject to: $\mathcal O_{\mathrm{Ig}}(\infty)$ consists of quotients $x/y$ of Laurent series over $A$ with $y$ of nonzero reduction; each $\mathcal O_{\mathrm{Ig}}(\ell)$ is the pullback of $\mathcal O_{\mathrm{Ig}}(\infty)$ along some $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$ with $\gamma\in\Gamma_0(M')$ moving $\infty$ to $\ell$; $\mathcal O_{\mathrm{Ig}}$ is injective and permuted by all such pullbacks; each $\mathcal O_{\mathrm{ss}}(s)$ meets the constants exactly in $A$, is fixed by all these pullbacks, contains an element $t$ with $t-a$ a unit for every $a\in A$, and receives the $R_0$-integral functions regular where $\hat\jmath$ is and whose residue is $s$-integral, with $f-a$ in the maximal ideal whenever $\mathrm{residue}\,a$ is the $s$-value of that residue. Descent data: a subfield $K_0\subseteq\overline{\mathbb Q}$ with $\overline{\mathbb Q}/K_0$ algebraic and $\pi\in K_0$; a henselian discrete valuation ring $A_0$ with an injective local map $\iota:A_0\to A$ whose image is $A\cap K_0$, with surjective induced residue map, uniformiser $\varpi_0$ satisfying $\iota\varpi_0=\pi$; the subfield $F_0$ of $\mathrm{fieldBar}\,q\,M'$ of elements all of whose Laurent coefficients lie in $K_0$, containing $\hat\jmath$, with $A_0$-algebra structure induced by $\iota$ on constants. Finally let $V$ be a valuation subring of $F_0$ contained in the trace of $\mathcal O_{\mathrm{Ig}}(\infty)$ to $F_0$, properly so. Then either (i) there are an $A_0$-subalgebra $B\subseteq F_0$ and a maximal ideal $\mathfrak m$ of $B$ such that $B$ is finitely generated, integrally closed in $F_0$, has fraction field $F_0$, every non-maximal prime containing $\varpi_0B$ is minimal over $\varpi_0B$, the localisation at every nonzero prime not containing $\varpi_0B$ is a valuation subring of $F_0$, the only $\ell'$ with $B\subseteq\mathcal O_{\mathrm{Ig}}(\ell')$ is $\infty$, no $\mathcal O_{\mathrm{ss}}(s)$ contains $B$, the trace of $\mathcal O_{\mathrm{Ig}}(\infty)$ to $F_0$ is the localisation of $B$ at some prime and equally at every minimal prime over $\varpi_0B$, $B\subseteq V$ with $\mathfrak m$ the contraction of the nonunits of $V$, $\hat\jmath\in B$ or $\hat\jmath^{-1}\in B$, and $A_0\to B_{\mathfrak m}$ is formally smooth; or (ii) there is $s\in W$ such that every $g\in F_0$ integral over $A_0[\hat\jmath]$ whose image lies in the maximal ideal of $\mathcal O_{\mathrm{ss}}(s)$ is a nonunit of $V$.
--
--   This is the dichotomy, at the prime $q=3$, governing valuation subrings of the descended field $F_0$ that refine the Gauss (i.e. $\ell=\infty$) Igusa ring: either such a refinement is centred on a formally smooth point of a finitely generated integral model adapted to the $\infty$-component, or the refinement is forced towards a supersingular Drinfeld ring. It feeds the local form of the same statement on the Igusa-tower leg of the semistable covering construction for full level $q^2M'$; the case $q\ge 5$ is handled by a companion statement with identical conclusion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_three.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_three
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
    (V : ValuationSubring ↥F₀)

    (hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q))
    (hVlt : ∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ∧ f ∉ V) :
    (∃ (B : Subalgebra A₀ ↥F₀) (𝔪 : Ideal ↥B) (_ : 𝔪.IsMaximal),

      B.FG ∧
      (∀ x : ↥F₀, _root_.IsIntegral ↥B x → x ∈ B) ∧
      (∀ x : ↥F₀, ∃ b c : ↥F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
        𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes) ∧
      (∀ 𝔭 : Ideal ↥B, 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭) →
        ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀)) ∧

      (∀ ℓ' : CuspidalType.ProjLine q, (∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OIg ℓ') → ℓ' = lineInfty q) ∧
      (∀ s : ↥W, ¬ ∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s) ∧
      (∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ↔
        ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
        ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧

      (∀ b : ↥B, (b : ↥F₀) ∈ V) ∧ (∀ b : ↥B, b ∈ 𝔪 ↔ (b : ↥F₀) ∈ V.nonunits) ∧

      ((⟨_, hjF₀⟩ : ↥F₀) ∈ B ∨ (⟨_, hjF₀⟩ : ↥F₀)⁻¹ ∈ B) ∧

      (algebraMap A₀ (Localization.AtPrime 𝔪)).FormallySmooth) ∨

    (∃ s : ↥W, (∀ g : ↥F₀, _root_.IsIntegral ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) g →
        (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) →
          g ∈ V.nonunits)) := by sorry
