-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_hecke_U_nodeUnit_eq_nodeUnit_comp
-- name    : ModularCurve.JHNeronObjectAtP.ptsSp_symm_hecke_U_nodeUnit_eq_nodeUnit_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/bf57f2af-8ed7-5c6d-bbb3-6a765cf13556
-- title:
--   Uₚ permutes node units of the glued Picard group by σ
-- statement:
--   Setting. Let $p$ be a prime and $M$ a positive integer with $p \mid M$ and $M/p$ nonzero, let $H \le (\mathbb{Z}/M)^\times$, and assume the Laurent $q$-expansion `jqModC ℚ` of $j$ lies in the full-level $q$-expansion function field `qExpFunctionFieldC ℚ ⊤` (hypothesis `hj`). Let $\mathfrak{X}$ be a Deligne–Rapoport datum `XHDRModelAtP p M H hpM hj` for the model $X_p(\Gamma_M(M,H))$ over $R_p$; in particular it carries a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with function field $\overline{F}_H =$ `xHFunctionFieldBar M H`, an isomorphism $\mathfrak{X}.\mathrm{eeta}$ of its underlying scheme with the generic fibre of the integral model, a smooth locus $\mathfrak{X}.\mathrm{smoothLocus}$, the two degeneracy morphisms $\mathfrak{X}.\pi$, $\mathfrak{X}.\pi_w$, an involution $\mathfrak{X}.w$ and diamond automorphisms $\mathfrak{X}.\mathrm{dia0}\,e$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA : A.LiesOverPrime p`), whose residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. Let $\Lambda$ be level data `JHNeronObjectAtP.LevelData p M H hpM A` (a structure morphism $\Lambda.\sigma_A$ to `base p`, a scheme $\Lambda.X$ with relative group law $\Lambda.L$, a bijection $\Lambda.\mathrm{pts}$ from $J_H(M/p)$ at the level subgroup `infSubgroup p M H hpM` onto generic points, and a bijection $\Lambda.\mathrm{ptsSp}$ of $\mathrm{Pic}^0$ of the residual function field $\overline{F} =$ `Fbar p M H hpM κ` $=$ `qExpFunctionFieldC κ (ΓN p M H hpM)` onto points over the residue point), and let $O$ be a Néron object `JHNeronObjectAtP p M H hpM A hA Λ` over it, with its scheme $O.G \to$ `base p`, relative group law, Hecke endomorphisms $O.\mathrm{hecke}$, finite set $O.\mathrm{ssFinset}$ of pairs of places of $\overline{F}$, and the bijection $O.\mathrm{ptsSp}$ from the glued group `GluedPic0 κ Fbar O.ssFinset` onto points of $O.G$ over the residue point. Finally let $\rho : R_p \to A$ satisfy $A.\mathrm{subtype} \circ \rho =$ `algebraMap (R p) (AlgebraicClosure ℚ)` (hypothesis `hρ`) and $\Lambda.\sigma_A = \operatorname{Spec}\rho$ (hypothesis `hσA`).
--
--   Hypothesis groups. Four dictionaries and three pieces of auxiliary data are assumed.
--
--   `hsp` (specialisation of point differences into the glued group, at level $M$): for every $i \in \{0,1\}$, every pair of $\overline{\mathbb{Q}}$-points $y_1, y_2$ of $\mathfrak{X}.\mathrm{Meta}.C$ (sections of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$), every pair of lifts $u_1, u_2$ over $\operatorname{Spec}\rho$ of the structure morphism `toBase p (ΓM M H) hj` such that $\mathrm{barPt}\,A$ followed by $u_k$ equals $y_k$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first pullback projection, and whose topological image lies in $\mathfrak{X}.\mathrm{smoothLocus}$, every pair of sections $u_{\kappa,1}, u_{\kappa,2}$ of the fibre of the integral model along $\mathrm{residue}_A \circ \rho$ compatible with $u_1, u_2$ along the residue map and splitting the second projection, every pair of closed points $P_1, P_2$ of the fibre curve model $\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho$ whose images under $\mathfrak{X}.\mathrm{efib}$ followed by the $i$-th component morphism $\mathfrak{X}.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,i$ are the closed points $u_{\kappa,k}(\mathrm{closedPoint})$, every degree-zero divisor $D_v$ on $\overline{F}_H$ equal to $\mathrm{single}(v(y_1)) - \mathrm{single}(v(y_2))$ for the places $v(y_k) = \mathfrak{X}.\mathrm{Meta}.\mathrm{pointEquivPlace}\,y_k$, and every admissible gluing datum $x$ whose first divisor component is $\mathrm{single}(v(P_1)) - \mathrm{single}(v(P_2))$ if $i = 0$ and $0$ otherwise, whose second divisor component is that same difference if $i = 1$ and $0$ otherwise, and whose unit component is $0$: there exists a point $s$ of $O.G$ over $\Lambda.\sigma_A$ with $(O.\mathrm{pts}(\mathrm{Pic}^0\text{-class of }D_v))$ equal to $\mathrm{barPt}\,A$ followed by $s$, and with $O.\mathrm{ptsSp}^{-1}$ of the restriction of $s$ along $\mathrm{resPt}\,A$ equal to the glued class `GluedPic0.mk O.ssFinset x`.
--
--   `hspΛ` (specialisation at level $M/p$, along $\pi$ and $\pi_w$): for every $i \in \{0,1\}$, points $y_1, y_2$ and lifts $u_1, u_2$ as above but with no smooth-locus condition, fibre sections $u_{\kappa,1}, u_{\kappa,2}$ subject to the same two compatibilities, closed points $Q_1, Q_2$ of $\mathfrak{X}.\mathrm{Mfib}$ whose $\mathfrak{X}.\mathrm{efib}$-images are the closed points of $u_{\kappa,k}$ followed by the fibre map of $\mathfrak{X}.\pi$ (if $i = 0$) or $\mathfrak{X}.\pi_w$ (if $i = 1$), a degree-zero divisor $D_v = \mathrm{single}(v(y_1)) - \mathrm{single}(v(y_2))$ on $\overline{F}_H$ and a degree-zero divisor $D_w = \mathrm{single}(v(Q_1)) - \mathrm{single}(v(Q_2))$ on $\overline{F}$: there exists a point $s_0$ of $\Lambda.X$ over $\Lambda.\sigma_A$ with $(\Lambda.\mathrm{pts}(O.\mathrm{degPts}\,i\,[D_v]))$ equal to $\mathrm{barPt}\,A$ followed by $s_0$, and $\Lambda.\mathrm{ptsSp}^{-1}$ of the restriction of $s_0$ along $\mathrm{resPt}\,A$ equal to the class of $D_w$.
--
--   `hdia0` (diamond operators on the fibre): for every unit $e$ of $\mathbb{Z}/(M/p)$ and every closed point $P$ of $\mathfrak{X}.\mathrm{Mfib}$, the point obtained by transporting $P$ through $\mathfrak{X}.\mathrm{efib}$, applying the fibre map of the automorphism $\mathfrak{X}.\mathrm{dia0}\,e$ (viewed as a morphism over the base), and transporting back through the inverse of $\mathfrak{X}.\mathrm{efib}$, is again closed, and its place is the image of the place of $P$ under the semilinear automorphism attached by `SemilinearAut.ofAlgAut` to `diamondActionModL κ (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) e)`.
--
--   `F, Finv, Fstar` with `hF, hFinv, hFstar` (Frobenius data on the residual Picard group): endomorphisms of $\mathrm{Pic}^0(\overline{F})$ with $F$ equal to the $q$-expansion Frobenius pushforward `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p`, with $F$ and $\mathrm{Finv}$ mutually inverse in both orders, and $\mathrm{Fstar}\,z = p \cdot \mathrm{Finv}\,z$.
--
--   `pb, hpb, δ, hδ` (the diamond at $p$): a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$, and an endomorphism $\delta$ of $\mathrm{Pic}^0(\overline{F})$ acting as the semilinear automorphism attached to `diamondActionModL κ (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) pb)`.
--
--   `αpull, degPull, hpull, hpull_mul, hpullsp` (degeneracy data): homomorphisms $\alpha_i : J_H(M/p) \to J_H(M)$ and morphisms $\mathrm{degPull}\,i$ from $\Lambda.X$ to $O.G$ over `base p`, for $i \in \{0,1\}$, such that $O.\mathrm{pts}(\alpha_i x)$ is $\Lambda.\mathrm{pts}(x)$ followed by $\mathrm{degPull}\,i$ for all $x$; such that each $\mathrm{degPull}\,i$ is additive, taking the $\Lambda.L$-product of two points over any test base to the $O.L$-product of their images; and such that, for every point $x$ of $\Lambda.X$ over $\mathrm{resPt}\,A \ggg \Lambda.\sigma_A$, the pair of $\mathrm{Pic}^0$-components `GluedPic0.toPic0Pair` of $O.\mathrm{ptsSp}^{-1}$ of ($x$ followed by $\mathrm{degPull}\,i$) equals $(\Lambda.\mathrm{ptsSp}^{-1}x, \mathrm{Fstar}(\Lambda.\mathrm{ptsSp}^{-1}x))$ for $i = 0$ and $(\mathrm{Fstar}(\Lambda.\mathrm{ptsSp}^{-1}x), \delta(\Lambda.\mathrm{ptsSp}^{-1}x))$ for $i = 1$.
--
--   `Wbar, wgen, hWbar, hwgen` (the involution): an endomorphism $\overline{W}$ of $J_H(M)$ given by the action of a semilinear automorphism $w_{\mathrm{gen}}$ of $\overline{F}_H$ over $\overline{\mathbb{Q}}$, such that whenever two $\overline{\mathbb{Q}}$-points $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ satisfy: $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, the first projection and $\mathfrak{X}.w$ equals $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection, then the place of $y'$ is $w_{\mathrm{gen}}$ applied to the place of $y$.
--
--   `S, hUPgen` (the Eichler relation): a set $S$ of primes such that, for all $x \in J_H(M)$, the value of the Hecke generator $U_p$ (`genOpH M H S (CohCarrier.Gen.U p _ hpM)`) at $x$ plus $\overline{W}x$ equals $\alpha_1(O.\mathrm{degPts}\,0\,x)$.
--
--   `σ, hσ` (the node permutation): a permutation $\sigma$ of $O.\mathrm{ssFinset}$ such that the second coordinate of $\sigma(n)$ is the first coordinate of $n$, for every $n$.
--
--   Conclusion. For every family of units $w : O.\mathrm{ssFinset} \to \mathrm{Additive}\,\kappa^\times$, the class $O.\mathrm{ptsSp}^{-1}$ of the composite of the point $O.\mathrm{ptsSp}(\mathrm{nodeUnit}\,w)$ with the Hecke endomorphism $O.\mathrm{hecke}\,S\,(U_p)$ equals $\mathrm{nodeUnit}(w \circ \sigma)$, where $\mathrm{nodeUnit}\,w$ denotes the class in `GluedPic0 κ Fbar O.ssFinset` of the admissible gluing datum $(0, 0, w)$.
--
--   This is the computation of the action of $U_p$ on the toric (node-unit) part of the glued degree-zero class group describing the special fibre at $p$ of the Néron object attached to $J_H(M)$ when $p \mid M$: on node units, $U_p$ acts simply by relabelling the nodes along $\sigma$, the permutation matching the second coordinate of a node pair with the first coordinate of its predecessor. It is used by [`ModularCurve.JHNeronObjectAtP.genOpH_U_mem_and_sp_genOpH_U_eq_nodeUnit_comp`](thm.html#ModularCurve.JHNeronObjectAtP.genOpH_U_mem_and_sp_genOpH_U_eq_nodeUnit_comp) and, through that, by the results on the toric and old lattices of the Tate module used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_hecke_U_nodeUnit_eq_nodeUnit_comp.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.JHNeronObjectAtP.ptsSp_symm_hecke_U_nodeUnit_eq_nodeUnit_comp
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
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

    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

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

    (σ : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσ : ∀ n : ↥O.ssFinset, (σ n).1.2 = n.1.1)
    :

    (∀ w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
      O.ptsSp.symm (schemeHomOverComp (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w))
          (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) =
        GluedPic0.nodeUnit O.ssFinset (w ∘ σ)) := by sorry
