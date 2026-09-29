-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_two
-- name    : ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/92c49bd1-f6d2-5bbb-9875-5818522c4236
-- title:
--   Gauss-component chart dichotomy for the descended model, q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'\neq 0$ be an integer with $q\nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $q$ is a non-unit. Let $W$ be a finite set of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$, assumed to consist exactly of the supersingular places (rational, affine geometric, with $j$-value in the supersingular set), and assume `modularFunctionFieldBar M' ≤ fieldBar q M'` via `hle`, where `fieldBar q M'` is the base change to $\overline{\mathbb Q}$ of the function field of level $q^2M'$ with subgroup the kernel of $(\mathbb Z/q^2M')^\times\to(\mathbb Z/q)^\times$. Further data: a constant reduction $R_0$ of `modularFunctionFieldBar M'` onto `modularFunctionFieldC (ResidueField A) M'` relative to $A$, compatible coefficientwise with reduction of Laurent series with $A$-integral coefficients; an element $\pi\in A$ with $\pi^{q^2-1}=q$; a primitive $q$-th root of unity $\zeta$; families of valuation subrings $\mathcal O_{\mathrm{Ig},\ell}$ of `fieldBar q M'` indexed by $\ell\in\mathbb P^1(\mathbb Z/q)$ and $\mathcal O_{\mathrm{ss},s}$ indexed by $s\in W$. The hypotheses on these families, summarised here, are: $\mathcal O_{\mathrm{Ig},\infty}$ consists of the ratios $x/y$ of Laurent series with $A$-integral coefficients whose denominator has nonzero reduction; the $\mathcal O_{\mathrm{Ig},\ell}$ are pairwise distinct, obtained from $\mathcal O_{\mathrm{Ig},\infty}$ by pullback along the level automorphisms `levelAutBar q M' ζ γ` for suitable $\gamma\in\Gamma_0(M')$, and permuted among themselves by all such pullbacks; each $\mathcal O_{\mathrm{ss},s}$ meets $\overline{\mathbb Q}$ in $A$, is invariant under the level automorphisms, contains an element $t$ with $t-a$ a unit for all $a\in A$, and is compatible with $R_0$ at $s$ for those $f$ in the integers of $R_0$ which are regular wherever $\hat\jmath$ is, the reduction of $f$ at $s$ being computed by $f-a$ lying in the maximal ideal of $\mathcal O_{\mathrm{ss},s}$. Finally, let $K_0\subseteq\overline{\mathbb Q}$ be a subfield with $\overline{\mathbb Q}/K_0$ algebraic and $\pi\in K_0$, let $A_0$ be a henselian discrete valuation domain with an injective local homomorphism $\iota\colon A_0\to A$ whose image is $A\cap K_0$ and which induces a surjection onto the residue field of $A$, with uniformiser $\varpi_0$ satisfying $\iota\varpi_0=\pi$; let $F_0$ be the subfield of `fieldBar q M'` of elements all of whose Laurent coefficients lie in $K_0$, an $A_0$-algebra via $\iota$, containing the image $\hat\jmath$ of $j$; and let $V$ be a valuation subring of $F_0$ contained in the trace of $\mathcal O_{\mathrm{Ig},\infty}$ to $F_0$ and strictly smaller than it. Then one of the following holds. Either there are an $A_0$-subalgebra $B\subseteq F_0$ and a maximal ideal $\mathfrak m$ of $B$ such that: $B$ is a finitely generated $A_0$-algebra, integrally closed in $F_0$, with $F_0$ as its field of fractions; every non-maximal prime of $B$ containing $\varpi_0B$ is minimal over $\varpi_0B$; for every nonzero prime $\mathfrak p$ not containing $\varpi_0B$ the localisation of $B$ at $\mathfrak p$ inside $F_0$ is a valuation subring; the only $\ell$ with $\mathcal O_{\mathrm{Ig},\ell}$ containing the image of $B$ is $\ell=\infty$; no $\mathcal O_{\mathrm{ss},s}$ contains the image of $B$; some prime of $B$, and every minimal prime over $\varpi_0B$, has localisation equal to the trace of $\mathcal O_{\mathrm{Ig},\infty}$ to $F_0$; $B\subseteq V$ and $\mathfrak m$ is the set of elements of $B$ that are non-units of $V$; either $\hat\jmath\in B$ or $\hat\jmath^{-1}\in B$; and $A_0\to B_{\mathfrak m}$ is formally smooth. Or else there is $s\in W$ such that every $g\in F_0$ integral over $A_0[\hat\jmath]$ whose image lies in the maximal ideal of $\mathcal O_{\mathrm{ss},s}$ is a non-unit of $V$.
--
--   This is the Igusa-chart dichotomy on the Gauss component of the descended integral model at the prime $q=2$: a valuation subring of the descended field $F_0$ strictly refining the traced Gauss ring is either centred on a formally smooth affine chart whose only Igusa ring is the one at $\ell=\infty$, or else is controlled by a supersingular (Drinfeld) place. It is the $q=2$ companion of the corresponding statement for $q\ge 5$, with identical conclusion, and feeds the local form of the same dichotomy used in the construction of the semistable covering of the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_two.lean

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

theorem ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_two
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
