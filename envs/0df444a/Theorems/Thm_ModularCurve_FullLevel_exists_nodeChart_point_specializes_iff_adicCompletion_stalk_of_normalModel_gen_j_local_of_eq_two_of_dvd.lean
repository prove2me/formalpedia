-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_nodeChart_point_specializes_iff_adicCompletion_stalk_of_normalModel_gen_j_local_of_eq_two_of_dvd
-- name    : ModularCurve.FullLevel.exists_nodeChart_point_specializes_iff_adicCompletion_stalk_of_normalModel_gen_j_local_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/e7bfc623-b7a0-55f4-9346-cf8a7b1de4fa
-- title:
--   Node chart at (ℓ,s) of the descended model, q=2
-- statement:
--   Throughout, $q$ is a prime with $q=2$, $M'$ is a nonzero natural number with $q\nmid M'$, and a natural number $\ell$ is fixed which is prime, satisfies $\ell\equiv 11\pmod{12}$ and divides $M'$ (this auxiliary prime is used only through the hypotheses `hℓ`, `hℓ12`, `hℓM'`; the final binder of the same name ranges over $\mathbb{P}^1(\mathbb{Z}/q)$ and shadows it, as does the bound variable of `hIg`). The function fields involved are: `modularFunctionFieldBar M'`, the subfield of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the full level-$M'$ modular function field; `fieldBar q M'`, the analogous base change to $\overline{\mathbb{Q}}$ of the function field of $X_H$ of level $q^2M'$ with $H=\ker\big((\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times\big)$; and, over a field $K$, `modularFunctionFieldC K M'`, the subfield of $\mathrm{LaurentSeries}(K)$ generated over $K$ by the $q$-expansions $j$ and $j(M'\cdot)$. Here $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with `hA : A.LiesOverPrime q`, i.e. $q$ lies in the nonunits of $A$; $W$ is a finite set of places of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$ (a place being a valuation subring containing the constants, distinct from the whole field, whose ideals are principal), and `hW` says that $W$ consists exactly of the supersingular places, namely the rational places which are affine geometric places and at which the evaluation of the geometric $j$-generator lies in the supersingular $j$-set for $q$. The hypothesis `hle` asserts the inclusion `modularFunctionFieldBar M' ≤ fieldBar q M'`.
--
--   Reduction data. $R_0$ is a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC (ResidueField A) M'`: a valuation subring $R_0.\mathrm{integers}$, a surjective residue homomorphism onto the target with kernel the maximal ideal, inducing $A$ on constants and compatible with the residue map of $A$, with the property that every nonzero element can be scaled by a constant into the integers with nonzero residue, together with a map on places preserving degrees and transporting divisors of functions with nonzero residue. The hypothesis `hR₀` states that for every Laurent series $y$ over $A$ whose coefficientwise image in $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ lies in `modularFunctionFieldBar M'`, that image lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over the residue field of $A$, is the coefficientwise residue of $y$.
--
--   A uniformising constant and a root of unity: $\pi\in\overline{\mathbb{Q}}$ with $\pi^{q^2-1}=q$ and $\pi\in A$, and $\zeta$ a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$.
--
--   The two families of valuation subrings of `fieldBar q M'`. The Igusa family $O_{\mathrm{Ig}}$ is indexed by $\mathbb{P}^1(\mathbb{Z}/q)$, the supersingular family $O_{\mathrm{SS}}$ by $W$. The hypothesis `hIg_inf` describes $O_{\mathrm{Ig}}$ at the point $[1:0]$: $f$ belongs to it precisely when there are Laurent series $x,y$ over $A$ with the coefficientwise residue of $y$ nonzero and $f\cdot y=x$ after coefficientwise inclusion of $A$ into $\overline{\mathbb{Q}}$. The hypothesis `hIg` says that for each point of $\mathbb{P}^1(\mathbb{Z}/q)$ there is $\gamma\in\Gamma_0(M')$ whose reduction in $\mathrm{GL}_2(\mathbb{Z}/q)$ carries $[1:0]$ to that point and for which the corresponding Igusa ring is the preimage of $O_{\mathrm{Ig}}([1:0])$ under the level automorphism `levelAutBar q M' ζ γ`; `hIg_inj` says $O_{\mathrm{Ig}}$ is injective; `hIg_perm` says that for every primitive $q$-th root of unity $\zeta'$ and every $\gamma\in\Gamma_0(M')$ the preimages of the rings $O_{\mathrm{Ig}}(\cdot)$ under `levelAutBar q M' ζ' γ` permute the family. For the supersingular family: `hSS_A` says that a constant from $\overline{\mathbb{Q}}$ lies in $O_{\mathrm{SS}}(s)$ if and only if it lies in $A$; `hSS_fix` says each $O_{\mathrm{SS}}(s)$ is invariant under preimage along every `levelAutBar q M' ζ' γ` with $\gamma\in\Gamma_0(M')$; `hSS_tr` provides, for each $s$, an element $t\in O_{\mathrm{SS}}(s)$ with $t-a$ a unit of $O_{\mathrm{SS}}(s)$ for every $a\in A$. The hypothesis `hSS_over` relates $R_0$ to $O_{\mathrm{SS}}$: for $s\in W$ and $f$ in $R_0.\mathrm{integers}$ such that $f$ has nonnegative order at every place of `modularFunctionFieldBar M'` at which the element $j$ (the coefficientwise image of the $q$-expansion `jq`, with its membership witness) has nonnegative order, and such that the $R_0$-residue of $f$ lies in the valuation subring of the place $s$, the image of $f$ in `fieldBar q M'` lies in $O_{\mathrm{SS}}(s)$, and moreover for every $a\in A$ whose residue equals the value of $s$ at the $R_0$-residue of $f$, the difference of that image and the constant $a$ lies in the maximal ideal of $O_{\mathrm{SS}}(s)$.
--
--   Descent data. $K_0$ is a subfield of $\overline{\mathbb{Q}}$ over which $\overline{\mathbb{Q}}$ is algebraic, with $\pi\in K_0$. $A_0$ is a Henselian discrete valuation domain with an injective local ring homomorphism $\iota:A_0\to A$ such that the image of $A_0$ in $\overline{\mathbb{Q}}$ is exactly $A\cap K_0$ (`hιK₀`) and such that $A_0\to$ residue field of $A$ is surjective (`hres`); $\varpi_0$ generates the maximal ideal of $A_0$ (`hϖ₀`) and $\iota(\varpi_0)=\pi$ in $\overline{\mathbb{Q}}$ (`hϖ₀π`). The field $F_0$ is a subfield of `fieldBar q M'` characterised by `hF₀`: an element lies in $F_0$ exactly when all its Laurent coefficients lie in $K_0$. By `hjF₀` the element $j$ lies in $F_0$, and $F_0$ carries an $A_0$-algebra structure whose structure map is, by `hj₀`, $a\mapsto \iota(a)$ viewed as a constant of `fieldBar q M'`.
--
--   The model. $X_0$ is a scheme with a morphism $\mathrm{toBase}_0 : X_0\to\operatorname{Spec} A_0$ which is proper, flat and locally of finite presentation, $X_0$ being integral; `hn₀` asserts that every stalk of $X_0$ is integrally closed; $\varphi_0$ is a ring isomorphism $F_0\cong$ the function field of $X_0$, compatible with constants in the sense that $\varphi_0$ applied to the image of $a\in A_0$ is `SemistableModel.baseToFunctionField toBase₀ a` (`hφ₀`). For a point $x$ of $X_0$ write $\mathcal{O}(x)$ for `SemistableModel.localRing X₀ φ₀ x`, the subring of $F_0$ obtained as the image under $\varphi_0^{-1}$ of the canonical map from the stalk at $x$ into the function field. The hypothesis `hdim` imposes relative dimension one: if $\eta$ lies over the closed point of $A_0$ and admits a strict specialisation, and $\eta\rightsquigarrow y$ with $y\neq\eta$, then $y$ is closed. Finally `gen` assigns to each index in $\mathbb{P}^1(\mathbb{Z}/q)\sqcup W$ a point of $X_0$ with: $\mathcal{O}(\mathrm{gen}(\mathrm{inl}\,\ell'))=\{f\in F_0: f\in O_{\mathrm{Ig}}(\ell')\}$ (`hgenIg`) and $\mathcal{O}(\mathrm{gen}(\mathrm{inr}\,s))=\{f\in F_0: f\in O_{\mathrm{SS}}(s)\}$ (`hgenSS`); each $\mathrm{gen}(i)$ lies over the closed point of $A_0$ (`hgen₀`); and a point over the closed point is of the form $\mathrm{gen}(i)$ if and only if it admits a strict specialisation (`hgen`).
--
--   Conclusion. For every point $\ell$ of $\mathbb{P}^1(\mathbb{Z}/q)$ and every $s\in W$ there exist an $A_0$-subalgebra $B\subseteq F_0$, a maximal ideal $\mathfrak{m}$ of $B$ and a point $x_0$ of $X_0$ such that:
--
--   (i) $B$ is a finitely generated $A_0$-algebra;
--
--   (ii) every element of $F_0$ integral over $\mathcal{O}(x_0)$ lies in $\mathcal{O}(x_0)$;
--
--   (iii) every element of $F_0$ is a quotient $b/c$ with $b,c\in B$, $c\neq 0$;
--
--   (iv) every prime ideal $\mathfrak{q}$ of $B$ which contains the ideal generated by the image of the maximal ideal of $A_0$ and is not maximal is a minimal prime over that ideal;
--
--   (v) for every $\eta\in X_0$ lying over the closed point of $A_0$ and admitting a strict specialisation, if $B\subseteq\mathcal{O}(\eta)$ then there is a prime $\mathfrak{q}$ of $B$ with $\mathcal{O}(\eta)$ equal to the localisation of $B$ at $\mathfrak{q}$ inside $F_0$, i.e. $x\in\mathcal{O}(\eta)$ iff $x=b/c$ with $b,c\in B$ and $c\notin\mathfrak{q}$;
--
--   (vi) conversely, for every minimal prime $\mathfrak{q}$ over the image of the maximal ideal of $A_0$ there is a point $\eta$ over the closed point, admitting a strict specialisation, with $\mathcal{O}(\eta)$ the localisation of $B$ at $\mathfrak{q}$ in the same sense;
--
--   (vii) the element $j$ (with its membership witness `hjF₀`) lies in $B$;
--
--   (viii) the image of $\varpi_0$ in $B$ lies in $\mathfrak{m}$;
--
--   (ix) $x_0$ lies over the closed point of $A_0$ and is a closed point of $X_0$ (every specialisation of $x_0$ equals $x_0$);
--
--   (x) $\mathcal{O}(x_0)$ is the localisation of $B$ at $\mathfrak{m}$ inside $F_0$;
--
--   (xi) for every index $i$, $\mathrm{gen}(i)\rightsquigarrow x_0$ holds if and only if $i=\mathrm{inl}\,\ell$ or $i=\mathrm{inr}\,s$;
--
--   (xii) $\mathrm{gen}(\mathrm{inl}\,\ell)\neq\mathrm{gen}(\mathrm{inr}\,s)$;
--
--   (xiii) the structure map $A_0\to B_{\mathfrak{m}}$ is not formally smooth;
--
--   (xiv) the stalk of $X_0$ at $x_0$ is a Noetherian ring, and there exists $w\geq 1$ such that $w$ is a unit in $A_0$ and there is a ring isomorphism
--   $$e:\ \widehat{\mathcal{O}}_{X_0,x_0}\ \xrightarrow{\ \sim\ }\ \widehat{A_0}[[X_0,X_1]]\big/\big(X_0X_1-\varpi_0^{\,w}\big),$$
--   where the left-hand side is the adic completion of the stalk at $x_0$ with respect to its maximal ideal, $\widehat{A_0}$ is the adic completion of $A_0$ at its maximal ideal, and $\varpi_0^{\,w}$ denotes the constant power series attached to the image of $\varpi_0^{\,w}$ in $\widehat{A_0}$; this isomorphism is compatible with constants, in that for every $a\in A_0$ the image under $e$ of the class in the completion of the germ at $x_0$ of the pullback of $a$ along $\mathrm{toBase}_0$ is the class of the constant power series of the image of $a$ in $\widehat{A_0}$.
--
--   This is the local chart at a crossing point of the special fibre of the descended full-level model: at the unique closed point where the Igusa component indexed by $\ell\in\mathbb{P}^1(\mathbb{Z}/q)$ meets the supersingular (Drinfeld) component attached to $s$, the completed local ring is an ordinary double point $X_0X_1=\varpi_0^w$ over the base, with $w$ invertible, and the point is not formally smooth over $A_0$; the case treated is $q=2$ under the rigidifying auxiliary level condition $\ell\equiv 11\pmod{12}$, $\ell\mid M'$. It feeds the corresponding Igusa-component and Drinfeld-component chart statements and the assembly of the semistable model of the full-level curve over the descent base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_nodeChart_point_specializes_iff_adicCompletion_stalk_of_normalModel_gen_j_local_of_eq_two_of_dvd.lean

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

theorem ModularCurve.FullLevel.exists_nodeChart_point_specializes_iff_adicCompletion_stalk_of_normalModel_gen_j_local_of_eq_two_of_dvd
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
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

    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))
    (φ₀ : ↥F₀ ≃+* X₀.functionField)
    (hφ₀ : ∀ a : A₀, φ₀ (algebraMap A₀ ↥F₀ a) = SemistableModel.baseToFunctionField toBase₀ a)
    (hdim : ∀ η y : X₀, toBase₀.base η = closedPoint A₀ → (∃ z : X₀, η ⤳ z ∧ z ≠ η) → η ⤳ y → y ≠ η →
      ∀ z : X₀, y ⤳ z → z = y)

    (gen : CuspidalType.ProjLine q ⊕ ↥W → X₀)
    (hgenIg : ∀ ℓ (f : ↥F₀), f ∈ SemistableModel.localRing X₀ φ₀ (gen (Sum.inl ℓ)) ↔ (f : ↥(fieldBar q M')) ∈ OIg ℓ)
    (hgenSS : ∀ s (f : ↥F₀), f ∈ SemistableModel.localRing X₀ φ₀ (gen (Sum.inr s)) ↔ (f : ↥(fieldBar q M')) ∈ OSS s)
    (hgen₀ : ∀ i, toBase₀.base (gen i) = closedPoint A₀)
    (hgen : ∀ x : X₀, toBase₀.base x = closedPoint A₀ → ((∃ i, x = gen i) ↔ ∃ y : X₀, x ⤳ y ∧ y ≠ x))
    (ℓ : CuspidalType.ProjLine q) (s : ↥W) :
    ∃ (B : Subalgebra A₀ ↥F₀) (𝔪 : Ideal ↥B) (_ : 𝔪.IsMaximal) (x₀ : X₀),

      B.FG ∧

      (∀ x : ↥F₀, _root_.IsIntegral ↥(SemistableModel.localRing X₀ φ₀ x₀) x → x ∈ SemistableModel.localRing X₀ φ₀ x₀) ∧
      (∀ x : ↥F₀, ∃ b c : ↥F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
        𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes) ∧
      (∀ η : X₀, toBase₀.base η = closedPoint A₀ → (∃ y : X₀, η ⤳ y ∧ y ≠ η) →
        (B : Set ↥F₀) ⊆ SemistableModel.localRing X₀ φ₀ η →
          ∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : ↥F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔
            ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
        ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ (∃ y : X₀, η ⤳ y ∧ y ≠ η) ∧
          ∀ x : ↥F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧

      (⟨_, hjF₀⟩ : ↥F₀) ∈ B ∧

      algebraMap A₀ ↥B ϖ₀ ∈ 𝔪 ∧
      toBase₀.base x₀ = closedPoint A₀ ∧ (∀ y : X₀, x₀ ⤳ y → y = x₀) ∧
      (∀ f : ↥F₀, f ∈ SemistableModel.localRing X₀ φ₀ x₀ ↔ ∃ b c : ↥B, c ∉ 𝔪 ∧ f * (c : ↥F₀) = (b : ↥F₀)) ∧

      (∀ i, gen i ⤳ x₀ ↔ (i = Sum.inl ℓ ∨ i = Sum.inr s)) ∧
      gen (Sum.inl ℓ) ≠ gen (Sum.inr s) ∧

      ¬ (algebraMap A₀ (Localization.AtPrime 𝔪)).FormallySmooth ∧

      (IsNoetherianRing (X₀.presheaf.stalk x₀) ∧
      ∃ (w : ℕ), 1 ≤ w ∧ IsUnit ((w : ℕ) : A₀) ∧

        ∃ e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
            (MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀) ⧸
              Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (maximalIdeal A₀) A₀)) * MvPowerSeries.X 1 -
                MvPowerSeries.C ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)}),
          ∀ a : A₀,
            e (algebraMap (X₀.presheaf.stalk x₀) _
                ((X₀.presheaf.germ ⊤ x₀ trivial).hom
                  (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
              Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))) := by sorry
