-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_forall_gaussBranch_descent_local_of_eq_three
-- name    : ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_forall_gaussBranch_descent_local_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/be88e766-3f9e-56ba-946a-b60a647a9446
-- title:
--   Igusa-chart dichotomy transported to every line, q=3
-- statement:
--   Throughout, $q$ is a prime subject to the hypothesis $q = 3$, and $M'$ is a nonzero level with $q \nmid M'$. The field $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` carries a valuation subring $A$ which lies over $q$ in the sense of `LiesOverPrime`, i.e. $q$ is a non-unit of $A$; write $k_A =$ `ResidueField A`. Two geometric function fields appear as intermediate fields of the Laurent series field $\overline{\mathbb Q}((t))$ over $\overline{\mathbb Q}$: `modularFunctionFieldBar M'`, the field generated over $\overline{\mathbb Q}$ by the coefficientwise images of the full level-$M'$ field `modularFunctionFieldFull M'`, and `fieldBar q M'`, the corresponding base change of the function field of level $\Gamma_H(q^2M')$ with $H$ the kernel of the reduction $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$; the hypothesis `hle` asserts the inclusion of the former in the latter. A finite set $W$ of places of `modularFunctionFieldC k_A M'` over $k_A$ is given, and `hW` says that $W$ consists exactly of the supersingular places `ssPlaces q M' k_A`, namely those places $w$ which are rational, are affine geometric places, and whose value `w.evalAt (jGeomGen k_A M')` lies in `ssJSet q k_A`.
--
--   The reduction datum is a `ConstantReduction` $R_0$ for $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC k_A M'`: a valuation subring $R_0.\mathrm{integers}$ of the geometric level-$M'$ field together with a surjective ring homomorphism $R_0.\mathrm{residue}$ onto `modularFunctionFieldC k_A M'` whose kernel is the maximal ideal, a map on places preserving degrees and compatible with orders of functions, membership of constants governed by $A$, and the existence, for each nonzero $f$, of a constant scaling $f$ into the integers with nonzero residue. The hypothesis `hR₀` requires that for every Laurent series $y$ with coefficients in $A$ whose coefficientwise image lies in `modularFunctionFieldBar M'`, that image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $k_A$, is the coefficientwise reduction of $y$. Further data: an element $\pi \in A$ with $\pi^{q^2-1} = q$, and an index $\zeta$, that is, a primitive $q$-th root of unity in $\overline{\mathbb Q}$, used to normalise the level automorphisms `levelAutBar q M' ζ γ` of `fieldBar q M'`.
--
--   Two families of valuation subrings of `fieldBar q M'` are given: $O_{\mathrm{Ig}}$ indexed by the projective line [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21) $= \mathbb P^1(\mathbb Z/q)$, and $O_{\mathrm{SS}}$ indexed by $W$. The Igusa group of hypotheses consists of: `hIg_inf`, which characterises $O_{\mathrm{Ig}}(\infty)$ at the distinguished point $\infty =$ `lineInfty q` $= [1:0]$ as the set of $f$ admitting Laurent series $x, y$ with coefficients in $A$, the reduction of $y$ nonzero, and $f\cdot y = x$ after pushing the coefficients into $\overline{\mathbb Q}$; `hIg`, which provides for each line $\ell$ some $\gamma \in \Gamma_0(M')$ with `redQ q γ • lineInfty q = ℓ` and $O_{\mathrm{Ig}}(\ell)$ equal to the preimage of $O_{\mathrm{Ig}}(\infty)$ under `levelAutBar q M' ζ γ`; `hIg_inj`, the injectivity of $\ell \mapsto O_{\mathrm{Ig}}(\ell)$; and `hIg_perm`, which says that for every index $\zeta'$ and every $\gamma \in \Gamma_0(M')$ the operation of taking preimages under `levelAutBar q M' ζ' γ` permutes the family, i.e. is induced by a permutation $\sigma$ of $\mathbb P^1(\mathbb Z/q)$.
--
--   The supersingular group consists of: `hSS_A`, which says that for each $s \in W$ a constant $x \in \overline{\mathbb Q}$ lies in $O_{\mathrm{SS}}(s)$ if and only if $x \in A$; `hSS_over`, which says that for $s \in W$ and $f$ in $R_0.\mathrm{integers}$ such that $f$ has non-negative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ at which the $j$-series $\hat\jmath$ (the coefficientwise image of `jq`) has non-negative order, if the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, then the image of $f$ in `fieldBar q M'` lies in $O_{\mathrm{SS}}(s)$, and for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of that $R_0$-residue, the difference of the image of $f$ and the constant $a$ lies in $O_{\mathrm{SS}}(s)$ and in its maximal ideal; `hSS_fix`, the invariance of each $O_{\mathrm{SS}}(s)$ under preimage along every `levelAutBar q M' ζ' γ` with $\gamma \in \Gamma_0(M')$; and `hSS_tr`, which provides for each $s$ an element $t \in O_{\mathrm{SS}}(s)$ such that $t - a$ lies in $O_{\mathrm{SS}}(s)$ and is a unit there for every constant $a \in A$.
--
--   The descent group consists of: a subfield $K_0 \subseteq \overline{\mathbb Q}$ with $\overline{\mathbb Q}$ algebraic over $K_0$ and $\pi \in K_0$; a henselian discrete valuation ring $A_0$ (a commutative domain) together with an injective local ring homomorphism $\iota : A_0 \to A$ such that the image of $A_0$ in $\overline{\mathbb Q}$ is exactly $A \cap K_0$ (`hιK₀`) and the composite of $\iota$ with the residue map of $A$ is surjective (`hres`); a uniformiser $\varpi_0$ generating the maximal ideal of $A_0$, with $\iota(\varpi_0) = \pi$ in $\overline{\mathbb Q}$; a subfield $F_0$ of `fieldBar q M'` characterised by `hF₀` as the set of elements all of whose Laurent coefficients lie in $K_0$; the hypothesis `hjF₀` that $\hat\jmath$, viewed in `fieldBar q M'` via `hle`, lies in $F_0$; and an $A_0$-algebra structure on $F_0$ whose structure map is, by `hj₀`, the composite of $\iota$ with $A \subseteq \overline{\mathbb Q} \to$ `fieldBar q M'`.
--
--   The final hypothesis `hinf` is the chart dichotomy for the line $\infty$: for every valuation subring $V$ of $F_0$ such that every element of $V$ maps into $O_{\mathrm{Ig}}(\infty)$, and such that some element of $F_0$ maps into $O_{\mathrm{Ig}}(\infty)$ without lying in $V$, one of the following two alternatives holds. The first alternative asserts the existence of an $A_0$-subalgebra $B \subseteq F_0$ and a maximal ideal $\mathfrak m$ of $B$ such that: $B$ is finitely generated; $B$ is integrally closed in $F_0$; every $x \in F_0$ is of the form $b/c$ with $b, c \in B$, $c \neq 0$; every prime $\mathfrak q$ of $B$ containing the image of the maximal ideal of $A_0$ and not maximal is a minimal prime over that image; for every nonzero prime $\mathfrak p$ of $B$ not containing that image there is a valuation subring $V_1$ of $F_0$ whose elements are exactly the $b/c$ with $b, c \in B$, $c \notin \mathfrak p$; the only line $\ell'$ with $B$ mapping into $O_{\mathrm{Ig}}(\ell')$ is $\infty$; for no $s \in W$ does $B$ map into $O_{\mathrm{SS}}(s)$; there is a prime $\mathfrak q$ of $B$ such that an $x \in F_0$ maps into $O_{\mathrm{Ig}}(\infty)$ if and only if $x = b/c$ with $b, c \in B$, $c \notin \mathfrak q$; the same description of $O_{\mathrm{Ig}}(\infty)$ holds for every minimal prime over the image of the maximal ideal of $A_0$; $B \subseteq V$ and $\mathfrak m$ is the set of $b \in B$ lying in $V.\mathrm{nonunits}$; $\hat\jmath \in B$ or $\hat\jmath^{-1} \in B$; and the structure map $A_0 \to B_{\mathfrak m} =$ `Localization.AtPrime 𝔪` is formally smooth. The second alternative asserts the existence of $s \in W$ such that every $g \in F_0$ integral over $A_0[\hat\jmath]$ whose image lies in $O_{\mathrm{SS}}(s)$ and in the maximal ideal of $O_{\mathrm{SS}}(s)$ lies in $V.\mathrm{nonunits}$.
--
--   The conclusion is that the same dichotomy holds for every line $\ell \in \mathbb P^1(\mathbb Z/q)$: for every valuation subring $V$ of $F_0$ all of whose elements map into $O_{\mathrm{Ig}}(\ell)$ and for which some element of $F_0$ maps into $O_{\mathrm{Ig}}(\ell)$ without lying in $V$, either there exist an $A_0$-subalgebra $B \subseteq F_0$ and a maximal ideal $\mathfrak m$ of $B$ satisfying the twelve clauses listed above with $\infty$ replaced by $\ell$ in the clauses on lines and on $O_{\mathrm{Ig}}$ — namely $B$ finitely generated, integrally closed in $F_0$, with $F_0$ as its field of fractions in the stated form, the clause on non-maximal primes over the image of the maximal ideal of $A_0$ being minimal primes over it, the clause realising the localisations at nonzero primes not containing that image as valuation subrings of $F_0$, the clause that $\ell$ is the only line whose Igusa ring contains the image of $B$, the clause that no $O_{\mathrm{SS}}(s)$ contains the image of $B$, the existence of a prime $\mathfrak q$ localising $B$ to $O_{\mathrm{Ig}}(\ell) \cap F_0$ in the stated quotient form, the same for every minimal prime over the image of the maximal ideal of $A_0$, the centring clauses $B \subseteq V$ and $\mathfrak m = \{b \in B : b \in V.\mathrm{nonunits}\}$, and the formal smoothness of $A_0 \to B_{\mathfrak m}$ — together with the clause on $\hat\jmath$ in the weakened form that either $\hat\jmath$ or $\hat\jmath^{-1}$ is of the shape $b/c$ with $b, c \in B$ and $c \notin \mathfrak m$, i.e. lies in $B_{\mathfrak m}$ rather than in $B$; or else there exists $s \in W$ such that every $g \in F_0$ integral over $A_0[\hat\jmath]$ whose image lies in $O_{\mathrm{SS}}(s)$ and in the maximal ideal of $O_{\mathrm{SS}}(s)$ lies in $V.\mathrm{nonunits}$.
--
--   Thus the conclusion is the hypothesis `hinf` with the Gauss line $\infty$ replaced by an arbitrary line $\ell$, at the cost of weakening the clause on the modular invariant $\hat\jmath$ from membership in $B$ to membership in the localisation $B_{\mathfrak m}$.
--
--   This is the level-transport step in the construction of the Igusa charts on the full-level modular curve over a henselian discrete valuation ring: the chart dichotomy established at the branch $\infty$ is spread, by means of the level automorphisms indexed by $\Gamma_0(M')$ acting transitively on $\mathbb P^1(\mathbb Z/q)$, to all branches. It is the $q = 3$ form of the statement, and it feeds [`ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_igusaRing_descent_local_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_igusaRing_descent_local_of_eq_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_forall_gaussBranch_descent_local_of_eq_three.lean

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

theorem ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_forall_gaussBranch_descent_local_of_eq_three
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

    (hinf : ∀ (V : ValuationSubring ↥F₀),
      (∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q)) →
      (∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ∧ f ∉ V) →
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
            g ∈ V.nonunits))) :
    ∀ (ℓ : CuspidalType.ProjLine q) (V : ValuationSubring ↥F₀),
      (∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg ℓ) →
      (∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg ℓ ∧ f ∉ V) →
      (∃ (B : Subalgebra A₀ ↥F₀) (𝔪 : Ideal ↥B) (_ : 𝔪.IsMaximal),

        B.FG ∧
        (∀ x : ↥F₀, _root_.IsIntegral ↥B x → x ∈ B) ∧
        (∀ x : ↥F₀, ∃ b c : ↥F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b) ∧
        (∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
          𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes) ∧
        (∀ 𝔭 : Ideal ↥B, 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭) →
          ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀)) ∧

        (∀ ℓ' : CuspidalType.ProjLine q, (∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OIg ℓ') → ℓ' = ℓ) ∧
        (∀ s : ↥W, ¬ ∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s) ∧
        (∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg ℓ ↔
          ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧
        (∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
          ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg ℓ ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧

        (∀ b : ↥B, (b : ↥F₀) ∈ V) ∧ (∀ b : ↥B, b ∈ 𝔪 ↔ (b : ↥F₀) ∈ V.nonunits) ∧

        ((∃ b c : ↥B, c ∉ 𝔪 ∧ (⟨_, hjF₀⟩ : ↥F₀) * (c : ↥F₀) = (b : ↥F₀)) ∨
        (∃ b c : ↥B, c ∉ 𝔪 ∧ (⟨_, hjF₀⟩ : ↥F₀)⁻¹ * (c : ↥F₀) = (b : ↥F₀))) ∧

        (algebraMap A₀ (Localization.AtPrime 𝔪)).FormallySmooth) ∨

      (∃ s : ↥W, (∀ g : ↥F₀, _root_.IsIntegral ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) g →
          (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) →
            g ∈ V.nonunits)) := by sorry
