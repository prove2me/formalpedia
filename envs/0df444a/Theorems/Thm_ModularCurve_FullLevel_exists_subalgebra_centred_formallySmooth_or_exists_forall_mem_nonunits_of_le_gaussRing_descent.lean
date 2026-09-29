-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent
-- name    : ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/937ad441-abbb-51e2-971f-0bd1b55a5d49
-- title:
--   Dichotomy for the Gauss component: smooth chart or supersingular place
-- statement:
--   Fix a prime $q \ge 5$, a level $M' \neq 0$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ consisting exactly of the supersingular places (rational, affine geometric, with $j$-value in `ssJSet q`), let $\mathrm{modularFunctionFieldBar}\,M' \le \mathrm{fieldBar}\,q\,M'$ via `hle`, and let $R_0$ be a `ConstantReduction` of $\mathrm{modularFunctionFieldBar}\,M'$ along $A$ (a valuation subring `integers`, a surjective residue map onto the reduced field with kernel the maximal ideal, compatible with $A$, its residue field, degrees and orders of places), assumed by `hR₀` to reduce coefficientwise Laurent series over $A$. Let $\pi \in A$ satisfy $\pi^{q^2-1} = q$, let $\zeta$ be a primitive $q$-th root of unity, and let $O_{\mathrm{Ig}}$, $O_{\mathrm{SS}}$ be families of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by $\mathbb P^1(\mathbb F_q)$ and by $W$ subject to: $O_{\mathrm{Ig}}(\infty)$ consists of the $f$ with $f\,y = x$ for Laurent series $x,y$ over $A$ with $y$ of nonzero reduction; every $\ell$ is obtained from $\infty$ by some $\gamma \in \Gamma_0(M')$ with $\mathrm{redQ}\,q\,\gamma \cdot \infty = \ell$ and $O_{\mathrm{Ig}}(\ell)$ the pullback of $O_{\mathrm{Ig}}(\infty)$ along `levelAutBar q M' ζ γ`; $O_{\mathrm{Ig}}$ is injective and the pullbacks along all `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$ permute the family; each $O_{\mathrm{SS}}(s)$ meets $\overline{\mathbb Q}$ in $A$, is fixed by all those automorphisms, contains an element $t$ with $t - a$ a unit for every $a \in A$, and receives elements of $R_0$'s integers which are regular wherever $j$ is and whose residue lies in $s$, with $f - a$ in the maximal ideal of $O_{\mathrm{SS}}(s)$ when $\mathrm{residue}_A(a)$ is the value of $s$ at the residue of $f$. Further, $K_0$ is a subfield of $\overline{\mathbb Q}$ containing $\pi$ with $\overline{\mathbb Q}/K_0$ algebraic, $A_0$ a henselian discrete valuation domain with an injective local ring map $\iota : A_0 \to A$ whose image is $A \cap K_0$, with surjective induced map to $\mathrm{ResidueField}\,A$ and uniformiser $\varpi_0$ satisfying $\iota(\varpi_0) = \pi$; $F_0$ is the subfield of $\mathrm{fieldBar}\,q\,M'$ of series all of whose coefficients lie in $K_0$, an $A_0$-algebra via $\iota$, containing $\hat\jmath$, the image of `jq`; finally $V$ is a valuation subring of $F_0$ contained in $O_{\mathrm{Ig}}(\infty) \cap F_0$ and properly so. The conclusion is a disjunction. Either there are an $A_0$-subalgebra $B \subseteq F_0$ and a maximal ideal $\mathfrak m$ of $B$ such that: $B$ is a finitely generated algebra, integrally closed in $F_0$, with $F_0$ its field of fractions; every prime of $B$ containing $\varpi_0 B$ that is not maximal is minimal over $\varpi_0 B$; every nonzero prime $\mathfrak p$ not containing $\varpi_0 B$ has its localisation equal to a valuation subring of $F_0$; $\infty$ is the only line $\ell'$ with $B \subseteq O_{\mathrm{Ig}}(\ell')$; no $O_{\mathrm{SS}}(s)$ contains $B$; $O_{\mathrm{Ig}}(\infty) \cap F_0$ is the localisation of $B$ at some prime, and at every minimal prime of $\varpi_0 B$; $B \subseteq V$ and $\mathfrak m$ is exactly the set of elements of $B$ lying in the nonunits of $V$; $\hat\jmath \in B$ or $\hat\jmath^{-1} \in B$; and $A_0 \to B_{\mathfrak m}$ is formally smooth. Or else there is a supersingular place $s \in W$ such that every $g \in F_0$ integral over $A_0[\hat\jmath]$ which lies in the maximal ideal of $O_{\mathrm{SS}}(s)$ is a nonunit of $V$.
--
--   This is the dichotomy, for a valuation subring $V$ refining the Gauss (Igusa line $\ell = \infty$) ring of the descended field $F_0$, between the place being the centre of a finitely generated, integrally closed $A_0$-chart that is formally smooth at $\mathfrak m$ and avoids both the other Igusa components and the Drinfeld rings at supersingular places, and the place lying over a supersingular place. It feeds the local form of the corresponding statement for an arbitrary Igusa line, obtained from this one by level transport.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open ModularCurve.FullLevel
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
