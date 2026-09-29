-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_descent_diamond_both_and_comp_hecke_U_eq_and_eq_verschiebung_of_blockOp_of_frobPullback_of_not_sq_dvd
-- name    : ModularCurve.JHNeronObjectAtP.exists_descent_diamond_both_and_comp_hecke_U_eq_and_eq_verschiebung_of_blockOp_of_frobPullback_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/d7b7dc95-c754-59d2-863e-7409abccbb73
-- title:
--   Descended diamond and Uₚ as D_Λ F on the p-fibre
-- statement:
--   Fix a prime $p$ and a natural number $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ subject to the hypothesis `hHp`: every unit $u$ of $\mathbb{Z}/M$ whose image under `ZMod.unitsMap` for the divisibility $(M/p) \mid M$ is $1$ lies in $H$ (so $H$ contains the kernel of the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$); $M/p$ is assumed non-zero. Assume `hj`: the $q$-expansion $j$-series `jqModC ℚ` lies in the function field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be a model package `XHDRModelAtP p M H hpM hj` for the curve of level `ΓM M H` over $R_p$: this carries, among its data, a curve model `𝔛.Meta` over $\overline{\mathbb{Q}}$ of the function field `xHFunctionFieldBar M H` together with the isomorphism `𝔛.eeta` onto the geometric generic fibre, a curve model `𝔛.Mfib A hA ρ hρ` of the special fibre over the residue field, the two component maps `𝔛.comp`, the degeneracy maps `𝔛.π`, `𝔛.πw`, the Atkin–Lehner isomorphism `𝔛.w`, the diamond isomorphisms `𝔛.dia0`, the comparison `𝔛.efib` and the smooth locus `𝔛.smoothLocus`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with `A.LiesOverPrime p`, that is $p$ is a non-unit of $A$, whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $\bar F =$ `Fbar p M H hpM κ` for the function field `qExpFunctionFieldC κ (ΓN p M H hpM)`. Let $\Lambda$ be level data `JHNeronObjectAtP.LevelData p M H hpM A`, consisting of a structure morphism `Λ.σA` over which the geometric point `barPt A` gives the generic point, a scheme `Λ.X` with morphism `Λ.f` to the base, a relative group law `Λ.L`, a bijection `Λ.pts` from $J_H(M/p)$ at level `infSubgroup p M H hpM` to the points of `Λ.f` over the generic point, and a bijection `Λ.ptsSp` from $\mathrm{Pic}^0(\kappa, \bar F)$ to the points over the special point; `Λ.f` is assumed separated and locally of finite type. Let $O$ be a `JHNeronObjectAtP p M H hpM A hA Λ`, with underlying scheme `O.G` and structure morphism `O.g`, commutative relative group law `O.L`, a bijection `O.pts` from $J_H(M)$ to the generic points, Hecke endomorphisms `O.hecke S t` indexed by the generators [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13), a reduction bijection `O.ptsSp` from the glued $\mathrm{Pic}^0$ attached to the finite set `O.ssFinset` of pairs of places of $\bar F$, degeneracy maps `O.degPts i : JH M H →+ JH (M/p) (infSubgroup p M H hpM)` and fibrewise abelian-quotient maps `O.abqFibre i`. Finally let $\rho : R_p \to A$ satisfy `hρ`: composing with the inclusion of $A$ gives the structure map $R_p \to \overline{\mathbb{Q}}$, and `hσA`: `Λ.σA` is $\operatorname{Spec}$ of $\rho$.
--
--   The hypotheses fall into the following groups.
--
--   (i) Two reduction dictionaries. `hsp` states, for each $i \in \{0,1\}$: given geometric points $y_1, y_2$ of `𝔛.Meta.C` over $\overline{\mathbb{Q}}$, $A$-points $u_1, u_2$ of the integral model over $\operatorname{Spec} \rho$ whose geometric specialisations are $y_1, y_2$ through `𝔛.eeta` followed by the first projection and whose images lie in `𝔛.smoothLocus`, residue-field points $u\kappa_1, u\kappa_2$ of the fibre which restrict to the reductions of $u_1, u_2$ and are sections of the second projection, closed points $P_1, P_2$ of the fibre curve model whose images under `𝔛.efib` followed by `𝔛.comp i` are the images of the closed point of $\kappa$ under $u\kappa_1$, $u\kappa_2$, a degree-zero divisor $Dv$ on `xHFunctionFieldBar M H` equal to $[y_1] - [y_2]$ under `𝔛.Meta.pointEquivPlace`, and an admissible gluing datum $x$ (a triple consisting of two divisors on $\bar F$ and a function from `O.ssFinset` to `Additive κˣ`, both divisors of degree zero and vanishing at the respective coordinates of the pairs in `O.ssFinset`) whose first component is $[P_1] - [P_2]$ if $i = 0$ and $0$ otherwise, whose second component is $[P_1] - [P_2]$ if $i = 1$ and $0$ otherwise, and whose third component is $0$ — then there exists a point $s$ of `O.g` over `Λ.σA` whose generic specialisation is the generic point `O.pts (Pic0.mk Dv)` and whose reduction corresponds under `O.ptsSp` to the class `GluedPic0.mk O.ssFinset x`. `hspΛ` is the corresponding dictionary for $\Lambda$: with the same generic data (the smooth-locus condition omitted), closed points $Q_1, Q_2$ of the fibre curve model whose images under `𝔛.efib` are the images of the closed point under $u\kappa_1$, $u\kappa_2$ composed with the fibre map of `𝔛.π` for $i = 0$ and of `𝔛.πw` otherwise, a degree-zero divisor $Dv = [y_1] - [y_2]$ and a degree-zero divisor $Dw = [Q_1] - [Q_2]$ on $\bar F$, there exists a point $s_0$ of `Λ.f` over `Λ.σA` whose generic specialisation is `Λ.pts (O.degPts i (Pic0.mk Dv))` and whose reduction corresponds under `Λ.ptsSp` to `Pic0.mk Dw`.
--
--   (ii) Diamond operators on the special fibre: `hdia0` asserts that for every unit $e$ of $\mathbb{Z}/(M/p)$ and every closed point $P$ of the fibre curve model, the image of $P$ under `𝔛.efib`, the fibre map of the diamond isomorphism `𝔛.dia0 e` and the inverse of `𝔛.efib` is again a closed point, and its place is the place of $P$ translated by the semilinear automorphism `SemilinearAut.ofAlgAut` of the diamond action `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at [`CuspForm.gammaLift (M/p) e`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36).
--
--   (iii) Frobenius data on $\mathrm{Pic}^0(\kappa, \bar F)$: additive endomorphisms `F`, `Finv`, `Fstar` with `hF`: `F` is the Frobenius pushforward `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p`; `hFinv`: `F` and `Finv` are mutually inverse; `hFstar`: `Fstar z = p • Finv z`.
--
--   (iv) A unit $pb$ of $\mathbb{Z}/(M/p)$ reducing to $p$ (`hpb`), and the additive endomorphism $\delta$ given (`hδ`) by the action of the diamond semilinear automorphism attached to [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36).
--
--   (v) Degeneracy data: homomorphisms `αpull i : JH (M/p) (infSubgroup p M H hpM) →+ JH M H` and morphisms `degPull i` from `Λ.f` to `O.g` over the base, for $i \in \{0,1\}$, with `hpull`: on generic points, `O.pts (αpull i x)` is `Λ.pts x` followed by `degPull i`; `hpullsp`: for every point $x$ of `Λ.f` over the special point, the pair of $\mathrm{Pic}^0$-classes attached by `GluedPic0.toPic0Pair` to the reduction of $x$ followed by `degPull i` is $(z, \mathtt{Fstar}\, z)$ for $i = 0$ and $(\mathtt{Fstar}\, z, \delta z)$ for $i = 1$, where $z$ is the class corresponding to $x$ under `Λ.ptsSp`; and `hpull_mul`: each `degPull i` is a homomorphism for the two relative group laws, in the sense that it carries `Λ.L.mul s x y` to `O.L.mul s` of the images.
--
--   (vi) Atkin–Lehner data: an additive endomorphism `Wbar` of $J_H(M)$, a semilinear automorphism `wgen` of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ with `hWbar`: `Wbar x = wgen • x`, and `hwgen`: whenever two geometric points $y, y'$ satisfy that $y'$ followed by `𝔛.eeta`, the first projection and `𝔛.w.hom` equals $y$ followed by `𝔛.eeta` and the first projection, the places of $y'$ and $y$ are related by the action of `wgen`.
--
--   (vii) A set $S$ of primes and the generic Eichler relation `hUPgen`: for all $x \in J_H(M)$, `genOpH M H S (CohCarrier.Gen.U p _ hpM) x + Wbar x = αpull 1 (O.degPts 0 x)`.
--
--   (viii) Combinatorial and Frobenius data on places: a permutation $\sigma$ of `O.ssFinset` with `hσ`: the second coordinate of $\sigma n$ is the first coordinate of $n$; a permutation $\Phi$ of the places of $\bar F$ with `hΦ`: $\Phi$ is `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`; and `hFdiv`: whenever two degree-zero divisors satisfy $D' = \Phi_* D$ (push-forward by `Finsupp.mapDomain`), one has `F (Pic0.mk D) = Pic0.mk D'`.
--
--   (ix) `hpull1sp`, the special-fibre description of `degPull 1` away from the supersingular pairs: for a degree-zero divisor $D$ on $\bar F$ and an admissible gluing datum $x_1$, if $D$ vanishes at $s.1$ and at $\Phi(s.1)$ for all $s \in$ `O.ssFinset`, the first component of $x_1$ is $p \cdot (\Phi^{-1})_* D$, the second component is the $\delta$-twist of $D$ by the diamond automorphism attached to [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36), and the third component is $0$, then the reduction of `Λ.ptsSp (Pic0.mk D)` followed by `degPull 1` is `GluedPic0.mk O.ssFinset x₁`.
--
--   (x) `hUPABQ`, the block form of $U_p$ on pairs: for every class $\xi$ in the glued $\mathrm{Pic}^0$, the pair associated by `GluedPic0.toPic0Pair` to the reduction of $\xi$ followed by `O.hecke S (CohCarrier.Gen.U p _ hpM)` equals `Pic0Pair.blockOp Fstar ((p - 1) • id) 0 (δ.comp F)` applied to the pair associated to $\xi$; that is, $(P,Q) \mapsto (\mathtt{Fstar}\,P + (p-1)Q,\ \delta(F Q))$.
--
--   (xi) `hUPKER`, two clauses about $U_p$ on gluing data: first, for admissible $x, x'$ such that the second divisor component of $x$ vanishes, the first component of $x$ vanishes at $\Phi(s.1)$ for all $s \in$ `O.ssFinset`, the first component of $x'$ is $p \cdot (\Phi^{-1})_*$ of the first component of $x$, the second component of $x'$ vanishes and the third component of $x'$ is the third component of $x$ precomposed with $\sigma$, the reduction of `GluedPic0.mk O.ssFinset x` followed by `O.hecke S (CohCarrier.Gen.U p _ hpM)` is `GluedPic0.mk O.ssFinset x'`; second, every class $\xi$ whose second $\mathrm{Pic}^0$-component vanishes is represented by an admissible $x$ with vanishing second divisor component and with first component vanishing at $\Phi(s.1)$ for all $s \in$ `O.ssFinset`.
--
--   (xii) Data over $\mathbb{F}_p$: an $\mathbb{F}_p$-algebra structure on $\kappa$, a point `σp` of the base over $\mathbb{F}_p$ with `hfac`: $\operatorname{Spec}$ of the structure map $\mathbb{F}_p \to \kappa$ followed by `σp` is the special point `resPt A ≫ Λ.σA`; a unit $d$ of $\mathbb{Z}/M$ whose image in $(\mathbb{Z}/(M/p))^\times$ is $p$ (`hd`); morphisms `q i` ($i \in \{0,1\}$) from the base change of `O.g` along `σp` to the base change of `Λ.f`, which are homomorphisms for the base-changed group laws (`hqmul`) and which descend the fibrewise maps `O.abqFibre i`, in the sense of the commuting square `hqbc` between the pullbacks along the special point and along `σp`; endomorphisms `U` and `D` of the base change of `O.g`, characterised by `hU` and `hD`: composing with the first projection gives the first projection followed by `O.hecke S (CohCarrier.Gen.U p _ hpM)`, respectively by `O.hecke S (CohCarrier.Gen.dia d)`; and endomorphisms `Fsch`, `Vsch` of the base change of `Λ.f` with `hFsch`: for every $\mathbb{F}_p$-algebra $B$ of characteristic $p$ and every $B$-point $x$, the point $x$ followed by `Fsch` is $\operatorname{Spec}$ of the $p$-power Frobenius of $B$ followed by $x$; and `hVF`: `Vsch` followed by `Fsch` is the multiplication-by-$p$ morphism `(Λ.L.baseChange σp).schemeNsmul p`.
--
--   The conclusion is the conjunction of two statements.
--
--   First, there exists an endomorphism $D_\Lambda$ of the base change of `Λ.f` along `σp` such that: $D_\Lambda$ is a homomorphism for the base-changed group law, i.e. for every test morphism $s$ to $\operatorname{Spec} \mathbb{F}_p$ and all points $x, y$ over $s$, the image of `(Λ.L.baseChange σp).mul s x y` under $D_\Lambda$ is the product of the images; `D` followed by `q 1` equals `q 1` followed by $D_\Lambda$; `D` followed by `q 0` equals `q 0` followed by $D_\Lambda$; and `U` followed by `q 1` equals `q 1` followed by `Fsch` and then by $D_\Lambda$, that is $q_1 \circ U = D_\Lambda \circ F \circ q_1$.
--
--   Second, for every test scheme $T$, every morphism $s : T \to \operatorname{Spec} \mathbb{F}_p$ and every point $x$ of the base change of `O.g` over $s$: if $x$ followed by `q 1` is the identity section `(Λ.L.baseChange σp).one s`, then $x$ followed by `U` and then by `q 0` equals $x$ followed by `q 0` and then by `Vsch`, that is $q_0(Ux) = V(q_0 x)$ on the kernel of $q_1$.
--
--   This is the Eichler–Shimura description, in the style of Deligne–Rapoport and Mazur–Wiles, of the Hecke operator $U_p$ on the two components of the special fibre of the Néron object of $J_H(M)$ at a prime $p$ exactly dividing $M$: over $\mathbb{F}_p$ the operator $U_p$ becomes the descended diamond operator composed with Frobenius on one abelian quotient, and acts as Verschiebung on the kernel of the other. It is used in the construction of the idempotent pair and of the two-step tower governing the Raynaud quotients and the projector components attached to the Néron object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_descent_diamond_both_and_comp_hecke_U_eq_and_eq_verschiebung_of_blockOp_of_frobPullback_of_not_sq_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.JHNeronObjectAtP.exists_descent_diamond_both_and_comp_hecke_U_eq_and_eq_verschiebung_of_blockOp_of_frobPullback_of_not_sq_dvd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hpM2 : ¬ p ^ 2 ∣ M) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    [IsSeparated Λ.f] [LocallyOfFiniteType Λ.f]
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
    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (σ : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσ : ∀ n : ↥O.ssFinset, (σ n).1.2 = n.1.1)

    (Φ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃ Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hΦ : ∀ v, Φ v = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v)
    (hFdiv : ∀ (D D' : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A))),
      (D' : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.mapDomain Φ (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) →
      F (Pic0.mk D) = Pic0.mk D')

    (hpull1sp : ∀ (D : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (x₁ : ↥(GluingData.admissible O.ssFinset)),
      (∀ s ∈ O.ssFinset, (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) s.1 = 0 ∧
        (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (Φ s.1) = 0) →
      (x₁ : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (p : ℤ) • Finsupp.mapDomain Φ.symm (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) →
      (x₁ : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb)) • (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) →
      (x₁ : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0 →
      O.ptsSp.symm (schemeHomOverComp (Λ.ptsSp (Pic0.mk D)) (degPull 1)) = GluedPic0.mk O.ssFinset x₁)

    (hUPABQ : (      ∀ ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
        GluedPic0.toPic0Pair O.ssFinset
            (O.ptsSp.symm (schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))) =
          AlgebraicCurve.Pic0Pair.blockOp Fstar (((p : ℤ) - 1) • AddMonoidHom.id _) 0 (δ.comp F)
            (GluedPic0.toPic0Pair O.ssFinset ξ)))

    (hUPKER : (∀ (x x' : ↥(GluingData.admissible O.ssFinset)),

      (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 = 0 →
      (∀ s ∈ O.ssFinset, (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 (Φ s.1) = 0) →

      (x' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (p : ℤ) • Finsupp.mapDomain Φ.symm
          (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 →
      (x' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 = 0 →
      (x' : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 =
        (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 ∘ σ →
      O.ptsSp.symm (schemeHomOverComp (O.ptsSp (GluedPic0.mk O.ssFinset x))
          (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) =
        GluedPic0.mk O.ssFinset x') ∧

    (∀ ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
      (GluedPic0.toPic0Pair O.ssFinset ξ).2 = 0 →
      ∃ x : ↥(GluingData.admissible O.ssFinset),
        (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 = 0 ∧
        (∀ s ∈ O.ssFinset, (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 (Φ s.1) = 0) ∧
        GluedPic0.mk O.ssFinset x = ξ))

    [Algebra (ZMod p) (ResidueField ↥A)]
    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ base p)
    (hfac : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A))) ≫ σp = resPt A ≫ Λ.σA)
    (d : (ZMod M)ˣ)
    (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))

    (q : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr σp O.g) (RelativeGroupLaw.baseChangeStr σp Λ.f))
    (hqmul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp O.g)),
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange σp).mul s x y) (q i) =
          (Λ.L.baseChange σp).mul s (NeronModelInfra.schemeHomOverComp x (q i)) (NeronModelInfra.schemeHomOverComp y (q i)))
    (hqbc : ∀ i : Fin 2,
        (O.abqFibre i).1 ≫ pullback.map Λ.f (resPt A ≫ Λ.σA) Λ.f σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) =
          pullback.map O.g (resPt A ≫ Λ.σA) O.g σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) ≫ (q i).1)

    (U D : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp O.g) (RelativeGroupLaw.baseChangeStr σp O.g))
    (hU : U.1 ≫ pullback.fst O.g σp = pullback.fst O.g σp ≫ (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1)
    (hD : D.1 ≫ pullback.fst O.g σp = pullback.fst O.g σp ≫ (O.hecke S (CohCarrier.Gen.dia d)).1)

    (Fsch Vsch : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f))
    (hFsch : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p]
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) (RelativeGroupLaw.baseChangeStr σp Λ.f)),
      (schemeHomOverComp x Fsch).1 = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x.1)
    (hVF : Vsch.1 ≫ Fsch.1 = (Λ.L.baseChange σp).schemeNsmul p)
    :

    (∃ DΛ : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f),

      (∀ {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp Λ.f)),
        schemeHomOverComp ((Λ.L.baseChange σp).mul s x y) DΛ =
          (Λ.L.baseChange σp).mul s (schemeHomOverComp x DΛ) (schemeHomOverComp y DΛ)) ∧
      schemeHomOverComp D (q 1) = schemeHomOverComp (q 1) DΛ ∧
      schemeHomOverComp D (q 0) = schemeHomOverComp (q 0) DΛ ∧
      schemeHomOverComp U (q 1) = schemeHomOverComp (schemeHomOverComp (q 1) Fsch) DΛ) ∧

    (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp O.g)),
      NeronModelInfra.schemeHomOverComp x (q 1) = (Λ.L.baseChange σp).one s →
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x U) (q 0) =
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x (q 0)) Vsch) := by sorry
