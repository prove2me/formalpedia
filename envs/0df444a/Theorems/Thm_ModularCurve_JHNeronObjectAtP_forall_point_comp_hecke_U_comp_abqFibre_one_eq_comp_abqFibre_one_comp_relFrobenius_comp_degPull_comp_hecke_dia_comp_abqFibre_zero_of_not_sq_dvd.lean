-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_forall_point_comp_hecke_U_comp_abqFibre_one_eq_comp_abqFibre_one_comp_relFrobenius_comp_degPull_comp_hecke_dia_comp_abqFibre_zero_of_not_sq_dvd
-- name    : ModularCurve.JHNeronObjectAtP.forall_point_comp_hecke_U_comp_abqFibre_one_eq_comp_abqFibre_one_comp_relFrobenius_comp_degPull_comp_hecke_dia_comp_abqFibre_zero_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/fea8b50c-19bc-5603-8ea5-a714cd0889a9
-- title:
--   Uₚ and Frobenius on κ̄-points of the Néron fibre
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ but $p^2 \nmid M$ (hypotheses `hpM`, `hpM2`), and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$ (hypothesis `hHp`). Assume the $q$-expansion $j$-series `jqModC ℚ` lies in the function field `qExpFunctionFieldC ℚ ⊤` (hypothesis `hj`), and let $\mathfrak{X}$ be an integral model datum `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over `R p`, carrying in particular the curve model `𝔛.Meta` of the geometric generic fibre, its comparison isomorphism `𝔛.eeta`, the degeneracy morphisms `𝔛.π`, `𝔛.πw`, the diamond isomorphisms `𝔛.dia0`, the Atkin–Lehner isomorphism `𝔛.w`, the smooth locus `𝔛.smoothLocus`, and the special-fibre data `𝔛.Mfib`, `𝔛.efib`, `𝔛.comp`.
--
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA : A.LiesOverPrime p`), whose residue field $\bar\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. Let $\Lambda$ be a level datum `JHNeronObjectAtP.LevelData p M H hpM A` — a scheme `Λ.X` with structure morphism `Λ.f` to `base p`, a relative group law, a bijection `Λ.pts` between $J_H(M/p)$ for the image subgroup `infSubgroup p M H hpM` and the generic sections of `Λ.f`, and a bijection `Λ.ptsSp` between $\mathrm{Pic}^0$ of `Fbar p M H hpM ↥(ResidueField ↥A)` and the sections of `Λ.f` over `resPt A ≫ Λ.σA` — and let $O$ be a Néron object `JHNeronObjectAtP p M H hpM A hA Λ` over it, with structure morphism `O.g`, group law, point bijection `O.pts : JH M H ≃ SchemeHomOver (genPt p) O.g`, Hecke endomorphisms `O.hecke S t` indexed by generators $t$ of the Hecke algebra, special-fibre gluing set `O.ssFinset`, degeneracy maps `O.degPts` on points and morphisms `O.abqFibre 0`, `O.abqFibre 1` from the base change of `O.g` to the base change of `Λ.f` over $\bar\kappa$. Let $\rho :$ `R p` $\to A$ satisfy $A.\mathrm{subtype} \circ \rho =$ the structure map of $\overline{\mathbb{Q}}$ (hypothesis `hρ`), and assume `Λ.σA` is induced by $\rho$ (hypothesis `hσA`).
--
--   The following groups of hypotheses are imposed.
--
--   (i) `hsp`, a specialisation dictionary for $O$: for each $i : \mathrm{Fin}\,2$, each pair of $\overline{\mathbb{Q}}$-points $y_1, y_2$ of `𝔛.Meta.C` over its base, lifts $u_1, u_2$ of these to morphisms over $\operatorname{Spec}\rho$ to the integral model (with the compatibilities $\mathrm{barPt}\,A \circ u_j =$ the point $y_j$ read through `𝔛.eeta` and the first projection, and with set-theoretic image inside `𝔛.smoothLocus`), residue-field points $u_{\kappa,1}, u_{\kappa,2}$ of the fibre over `(residue ↥A) ∘ ρ` reducing $u_1, u_2$ and sectioning the second projection, closed points $P_1, P_2$ of `(𝔛.Mfib A hA ρ hρ).C` whose images under `𝔛.efib` followed by `𝔛.comp … i` are the closed points carried by $u_{\kappa,1}, u_{\kappa,2}$, a degree-zero divisor $D_v$ on `xHFunctionFieldBar M H` equal to the difference of the places attached to $y_1$ and $y_2$, and an admissible gluing datum $x$ for `O.ssFinset` whose first component is the difference of the places of $P_1$ and $P_2$ when $i = 0$ and $0$ otherwise, whose second component is that same difference when $i = 1$ and $0$ otherwise, and whose unit component is $0$: there exists a section $s$ of `O.g` over `Λ.σA` with $(O.\mathrm{pts}(\,[D_v]\,))_1 = \mathrm{barPt}\,A$ followed by $s$, and with `O.ptsSp.symm` of the restriction of $s$ along `resPt A` equal to the class of $x$ in `GluedPic0`.
--
--   (ii) `hspΛ`, the corresponding dictionary for $\Lambda$: for each $i : \mathrm{Fin}\,2$, points $y_1, y_2$ with lifts $u_1, u_2$ and the compatibility with `𝔛.eeta`, residue-field points $u_{\kappa,1}, u_{\kappa,2}$ reducing them and sectioning the second projection, closed points $Q_1, Q_2$ of `(𝔛.Mfib A hA ρ hρ).C` whose images under `𝔛.efib` are the closed points obtained by transporting $u_{\kappa,j}$ along the fibre map of `𝔛.π` if $i = 0$ and of `𝔛.πw` otherwise, a degree-zero divisor $D_v$ equal to the difference of the places of $y_1$ and $y_2$, and a degree-zero divisor $D_w$ on `Fbar p M H hpM (ResidueField ↥A)` equal to the difference of the places of $Q_1$ and $Q_2$: there exists a section $s_0$ of `Λ.f` over `Λ.σA` with $(\Lambda.\mathrm{pts}(O.\mathrm{degPts}\,i\,[D_v]))_1 = \mathrm{barPt}\,A$ followed by $s_0$, and `Λ.ptsSp.symm` of the restriction of $s_0$ along `resPt A` equal to $[D_w]$.
--
--   (iii) `hdia0`: for every unit $e$ of $\mathbb{Z}/(M/p)$ and every closed point $P$ of `(𝔛.Mfib A hA ρ hρ).C`, the point obtained by transporting $P$ through `𝔛.efib`, the fibre map of the isomorphism `𝔛.dia0 e` and the inverse of `𝔛.efib` is again a closed point, and its place is the image of the place of $P$ under the semilinear automorphism attached to `diamondActionModL` at the lift [`CuspForm.gammaLift (M / p) e`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36).
--
--   (iv) Frobenius data: additive endomorphisms $F, F^{-1}, F^{*}$ of $\mathrm{Pic}^0$ of `Fbar p M H hpM (ResidueField ↥A)` with $F =$ `qExpFrobeniusPushforwardModL` at $p$ (`hF`), $F \circ F^{-1}$ and $F^{-1} \circ F$ both the identity (`hFinv`), and $F^{*}z = p \cdot F^{-1}z$ (`hFstar`).
--
--   (v) Diamond data: a unit $pb$ of $\mathbb{Z}/(M/p)$ whose value is $p$ (`hpb`), and an additive endomorphism $\delta$ acting as the semilinear automorphism attached to `diamondActionModL` at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) (`hδ`).
--
--   (vi) Degeneracy data: additive maps $\alpha_i : J_H(M/p) \to J_H(M)$ and morphisms $\mathrm{degPull}\,i$ from `Λ.f` to `O.g` over the base, compatible on generic points by `hpull` ($(O.\mathrm{pts}(\alpha_i x))_1 = (\Lambda.\mathrm{pts}\,x)_1$ followed by $\mathrm{degPull}\,i$), and compatible on the special fibre by `hpullsp`: for every section $x$ of `Λ.f` over `resPt A ≫ Λ.σA`, the pair `GluedPic0.toPic0Pair` of `O.ptsSp.symm` of $x$ composed with $\mathrm{degPull}\,i$ is $(\Lambda.\mathrm{ptsSp.symm}\,x, F^{*}(\Lambda.\mathrm{ptsSp.symm}\,x))$ for $i = 0$ and $(F^{*}(\Lambda.\mathrm{ptsSp.symm}\,x), \delta(\Lambda.\mathrm{ptsSp.symm}\,x))$ for $i = 1$.
--
--   (vii) Atkin–Lehner data: an additive endomorphism $\bar W$ of $J_H(M)$ and a semilinear automorphism `wgen` of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ with $\bar W x = \mathrm{wgen} \cdot x$ (`hWbar`), such that whenever two $\overline{\mathbb{Q}}$-points $y, y'$ satisfy $y'$ read through `𝔛.eeta`, the first projection and `𝔛.w.hom` equals $y$ read through `𝔛.eeta` and the first projection, the place of $y'$ is $\mathrm{wgen}$ applied to the place of $y$ (`hwgen`).
--
--   (viii) A set of primes $S$ and the relation `hUPgen`: for every $x \in J_H(M)$, $U_p x + \bar W x = \alpha_1(O.\mathrm{degPts}\,0\,x)$, where $U_p$ denotes `genOpH M H S (CohCarrier.Gen.U p _ hpM)`.
--
--   (ix) Characteristic and Frobenius structure over $\bar\kappa$: `hp0` states that $p = 0$ in the global sections of the base change of `Λ.f` along `resPt A ≫ Λ.σA`, and `hFrobΛ` states that the absolute $p$-power Frobenius `Scheme.frobenius` of that base-changed scheme, followed by the first projection and `Λ.f`, equals the second projection followed by `resPt A ≫ Λ.σA`.
--
--   (x) A unit $d_M$ of $\mathbb{Z}/M$ reducing to $pb$ in $(\mathbb{Z}/(M/p))^\times$ (`hdM`).
--
--   Under these hypotheses the conclusion is the following identity of morphisms of schemes, tested on all $\bar\kappa$-points. Write $G_{\bar\kappa}$ for the base change `RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) O.g` with structure morphism the corresponding `baseChangeStr`, and $\Lambda_{\bar\kappa}$ for the analogous base change of `Λ.f`. Then for every $x$ which is a morphism $\operatorname{Spec}\bar\kappa \to G_{\bar\kappa}$ whose composite with the structure morphism is the identity of $\operatorname{Spec}\bar\kappa$, the underlying composites agree:
--   $$x \cdot \big(U_{\bar\kappa}\ \text{followed by}\ O.\mathrm{abqFibre}\,1\big) \;=\; x \cdot \big(O.\mathrm{abqFibre}\,1,\ \text{then}\ \Phi,\ \text{then}\ (\mathrm{degPull}\,0)_{\bar\kappa},\ \text{then}\ \langle d_M\rangle_{\bar\kappa},\ \text{then}\ O.\mathrm{abqFibre}\,0\big),$$
--   where $U_{\bar\kappa}$ is the base change to $\bar\kappa$ of the Hecke endomorphism `O.hecke S (CohCarrier.Gen.U p _ hpM)` of $O.G$ (the pullback map with identity on the base, the required commutations being those of `O.hecke`), $\langle d_M\rangle_{\bar\kappa}$ is likewise the base change of `O.hecke S (CohCarrier.Gen.dia dM)`, $(\mathrm{degPull}\,0)_{\bar\kappa}$ is the base change of $\mathrm{degPull}\,0$ from $\Lambda_{\bar\kappa}$ to $G_{\bar\kappa}$, and $\Phi$ is the endomorphism of $\Lambda_{\bar\kappa}$ over $\bar\kappa$ determined by the requirements that its composite with the first projection be the absolute $p$-power Frobenius of $\Lambda_{\bar\kappa}$ followed by the first projection, and its composite with the second projection be the second projection (this being legitimate by `hp0` and `hFrobΛ`). Both sides are morphisms from $G_{\bar\kappa}$ to $\Lambda_{\bar\kappa}$ over $\bar\kappa$, and the asserted equality is of their underlying composites with $x$, that is, of morphisms $\operatorname{Spec}\bar\kappa \to \Lambda_{\bar\kappa}$.
--
--   This is the pointwise form, over the algebraically closed residue field at a place above $p$, of the Eichler–Shimura type relation expressing the Hecke operator $U_p$ at a prime exactly dividing the level in terms of Frobenius, a degeneracy pull-back and a diamond operator, read through the component maps `O.abqFibre 0`, `O.abqFibre 1` of the special fibre of the Néron object. It is used, together with a rigidity principle identifying morphisms that agree on $\bar\kappa$-points, by [`ModularCurve.JHNeronObjectAtP.exists_abqFibre_one_comp_baseChange_hecke_U_eq_comp_relFrobenius_comp_abqFibre_one_of_not_sq_dvd`](thm.html#ModularCurve.JHNeronObjectAtP.exists_abqFibre_one_comp_baseChange_hecke_U_eq_comp_relFrobenius_comp_abqFibre_one_of_not_sq_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_forall_point_comp_hecke_U_comp_abqFibre_one_eq_comp_abqFibre_one_comp_relFrobenius_comp_degPull_comp_hecke_dia_comp_abqFibre_zero_of_not_sq_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.JHNeronObjectAtP.forall_point_comp_hecke_U_comp_abqFibre_one_eq_comp_abqFibre_one_comp_relFrobenius_comp_degPull_comp_hecke_dia_comp_abqFibre_zero_of_not_sq_dvd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt A ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (S : Set ℕ)
    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))

    (hp0 : (p : Γ((RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f), ⊤)) = 0)

    (hFrobΛ : (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f) p 1 Fact.out hp0 ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA)) ≫ Λ.f =
      pullback.snd Λ.f (resPt A ≫ Λ.σA) ≫ (resPt A ≫ Λ.σA))

    (dM : (ZMod M)ˣ) (hdM : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) dM = pb) :
    ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g),
      x.1 ≫ (NeronModelInfra.schemeHomOverComp
        (⟨pullback.map O.g (resPt A ≫ Λ.σA) O.g (resPt A ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1 (𝟙 _) (𝟙 _)
            (by rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).2).symm)
            (by rw [Category.comp_id, Category.id_comp]),
          by rw [RelativeGroupLaw.baseChangeStr, pullback.lift_snd, Category.comp_id]⟩ :
          SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g))
        (O.abqFibre 1)).1 =
      x.1 ≫ (NeronModelInfra.schemeHomOverComp (O.abqFibre 1)
        (NeronModelInfra.schemeHomOverComp
          (⟨pullback.lift (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f) p 1 Fact.out hp0 ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA)) (pullback.snd Λ.f (resPt A ≫ Λ.σA)) hFrobΛ,
            pullback.lift_snd _ _ _⟩ :
            SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f))
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp
          (⟨pullback.map Λ.f (resPt A ≫ Λ.σA) O.g (resPt A ≫ Λ.σA) (degPull 0).1 (𝟙 _) (𝟙 _)
              (by rw [Category.comp_id]; exact ((degPull 0).2).symm)
              (by rw [Category.comp_id, Category.id_comp]),
            by rw [RelativeGroupLaw.baseChangeStr, RelativeGroupLaw.baseChangeStr, pullback.lift_snd, Category.comp_id]⟩ :
            SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g))
          (⟨pullback.map O.g (resPt A ≫ Λ.σA) O.g (resPt A ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.dia dM)).1 (𝟙 _) (𝟙 _)
              (by rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.dia dM)).2).symm)
              (by rw [Category.comp_id, Category.id_comp]),
            by rw [RelativeGroupLaw.baseChangeStr, pullback.lift_snd, Category.comp_id]⟩ :
            SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)))
          (O.abqFibre 0)))).1 := by sorry
