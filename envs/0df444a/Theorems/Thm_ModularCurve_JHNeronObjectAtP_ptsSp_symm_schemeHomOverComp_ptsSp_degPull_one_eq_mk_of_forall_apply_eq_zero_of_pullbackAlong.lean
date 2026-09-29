-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_ptsSp_degPull_one_eq_mk_of_forall_apply_eq_zero_of_pullbackAlong
-- name    : ModularCurve.JHNeronObjectAtP.ptsSp_symm_schemeHomOverComp_ptsSp_degPull_one_eq_mk_of_forall_apply_eq_zero_of_pullbackAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/553a2c7a-e10e-507b-a4b5-9194e42e4e8e
-- title:
--   Special fibre of the second degeneracy pull-back on Pic⁰
-- statement:
--   Throughout, $p$ is a prime and $M$ a nonzero natural number with $p \mid M$ and $M/p \neq 0$; $H$ is a subgroup of $(\mathbb{Z}/M)^\times$, and $H' =$ `infSubgroup p M H hpM` denotes the image of $H$ under the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$. The hypothesis `hj` says that the $q$-expansion `jqModC ℚ` of $j$ lies in the level-one $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`. The datum $\mathfrak{X}$ is an `XHDRModelAtP p M H hpM hj`, the Deligne–Rapoport-style integral model package at level $\Gamma_M(M,H)$ over `R p`, carrying in particular a curve model $\mathfrak{X}.\mathtt{Meta}$ of the generic fibre with function field `xHFunctionFieldBar M H`, the isomorphism `eeta` onto the base change to $\overline{\mathbb{Q}}$, the Atkin–Lehner isomorphism $\mathfrak{X}.w$, the degeneracy maps $\mathfrak{X}.\pi$, $\mathfrak{X}.\pi_w$, the diamond isomorphisms $\mathfrak{X}.\mathtt{dia0}$, the smooth locus, and the reduced-fibre curve model $\mathfrak{X}.\mathtt{Mfib}\,A\,hA\,\rho\,h\rho$ with its comparison maps `efib`, `comp i`.
--
--   Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with `A.LiesOverPrime p` (that is, $p$ lies in the nonunits of $A$), whose residue field $\kappa =$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed; $\Lambda$ is a `JHNeronObjectAtP.LevelData p M H hpM A`, providing a structure morphism $\Lambda.\sigma_A$ over `base p`, a group scheme $\Lambda.f$ with relative group law, a dictionary $\Lambda.\mathtt{pts}$ between $J_{H'}(M/p) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \overline{F}_{H'}(M/p))$ and generic sections, and a dictionary $\Lambda.\mathtt{ptsSp}$ between $\mathrm{Pic}^0(\kappa, \overline{F})$, where $\overline{F} =$ `Fbar p M H hpM κ` $=$ `qExpFunctionFieldC κ (ΓN p M H hpM)`, and sections over `resPt A ≫ Λ.σA`; and $O$ is a `JHNeronObjectAtP p M H hpM A hA Λ`, the corresponding object at level $\Gamma_H(M)$ with group scheme $O.g$, dictionary $O.\mathtt{pts}$ on $J_H(M)$, supersingular-node index set $O.\mathtt{ssFinset}$ (a finite set of pairs of places of $\overline{F}$), special-fibre dictionary $O.\mathtt{ptsSp}$ with values in the glued Picard group `GluedPic0 κ (Fbar …) O.ssFinset`, and degeneracy push-forwards $O.\mathtt{degPts}\,i : J_H(M) \to J_{H'}(M/p)$. Finally $\rho :$ `R p` $\to A$ satisfies $h\rho$: composing $\rho$ with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ gives the structure map `algebraMap (R p) (AlgebraicClosure ℚ)`, and $h\sigma_A$ identifies $\Lambda.\sigma_A$ with `Spec.map (CommRingCat.ofHom ρ)`.
--
--   The hypotheses then fall into the following groups; the internal clauses of the first two are long and are summarised here.
--
--   `hsp` (the point dictionary for $O$ at the special fibre): for every $i \in \{0,1\}$, every pair of $\overline{\mathbb{Q}}$-points $y_1, y_2$ of $\mathfrak{X}.\mathtt{Meta}.C$ (sections of $\mathfrak{X}.\mathtt{Meta}.\mathtt{toBase}$), every pair of $A$-valued sections $u_1, u_2$ of `toBase p (ΓM M H) hj` over `Spec.map (CommRingCat.ofHom ρ)` whose generic restrictions along `barPt A` are $y_1$, $y_2$ read through `eeta` followed by `pullback.fst` and whose set-theoretic images lie in $\mathfrak{X}$'s smooth locus, every pair of sections $u_{\kappa 1}, u_{\kappa 2}$ of the fibre over $\kappa$ compatible with $u_1, u_2$ along the residue map and splitting the projection to $\mathrm{Spec}\,\kappa$, every pair of closed points $P_1, P_2$ of $\mathfrak{X}.\mathtt{Mfib}$ whose images under `efib` followed by `comp i` are the closed points of $u_{\kappa 1}, u_{\kappa 2}$, every degree-zero divisor $D_v$ of `xHFunctionFieldBar M H` equal to $(y_1) - (y_2)$ under $\mathfrak{X}.\mathtt{Meta}.\mathtt{pointEquivPlace}$, and every admissible gluing datum $x$ (an element of `GluingData.admissible O.ssFinset`) whose first component is $(P_1) - (P_2)$ if $i = 0$ and $0$ otherwise, whose second component is $(P_1) - (P_2)$ if $i = 1$ and $0$ otherwise (places read off by $\mathfrak{X}.\mathtt{Mfib}.\mathtt{placeOfPoint}$), and whose third (node) component is $0$: there is a section $s$ of $O.g$ over $\Lambda.\sigma_A$ with $O.\mathtt{pts}(\mathrm{Pic}^0\text{-class of } D_v)$ equal to `barPt A` followed by $s$, and with $O.\mathtt{ptsSp}^{-1}$ of the restriction of $s$ along `resPt A` equal to the class `GluedPic0.mk O.ssFinset x`.
--
--   `hspΛ` (the analogous dictionary for $\Lambda$, with $\mathrm{Pic}^0(\kappa,\overline{F})$ in place of the glued group): for every $i \in \{0,1\}$, generic points $y_1, y_2$ with lifts $u_1, u_2$ and residual sections $u_{\kappa 1}, u_{\kappa 2}$ as above (here without the smooth-locus condition), closed points $Q_1, Q_2$ of $\mathfrak{X}.\mathtt{Mfib}$ whose images under `efib` are the images of the closed point of $\kappa$ under $u_{\kappa j}$ followed by the fibre map of $\mathfrak{X}.\pi$ (for $i = 0$) or of $\mathfrak{X}.\pi_w$ (otherwise), a degree-zero divisor $D_v$ of `xHFunctionFieldBar M H` equal to $(y_1) - (y_2)$, and a degree-zero divisor $D_w$ of $\overline{F}$ equal to $(Q_1) - (Q_2)$: there is a section $s_0$ of $\Lambda.f$ over $\Lambda.\sigma_A$ with $\Lambda.\mathtt{pts}(O.\mathtt{degPts}\,i\,[D_v])$ equal to `barPt A` followed by $s_0$, and $\Lambda.\mathtt{ptsSp}^{-1}$ of the restriction of $s_0$ along `resPt A` equal to $[D_w]$.
--
--   `hdia0` (diamond operators on the reduced fibre): for every $e \in (\mathbb{Z}/(M/p))^\times$ and every closed point $P$ of $\mathfrak{X}.\mathtt{Mfib}.C$, the image of $P$ under `efib`, the fibre map of the diamond isomorphism $\mathfrak{X}.\mathtt{dia0}\,e$, and the inverse of `efib` is again a closed point, and its place is $\mathrm{ofAlgAut}$ of `diamondActionModL κ (M/p) H' (CuspForm.gammaLift (M/p) e)` acting on the place of $P$.
--
--   Frobenius group (`F`, `Finv`, `Fstar`, `hF`, `hFinv`, `hFstar`): three endomorphisms of $\mathrm{Pic}^0(\kappa, \overline{F})$ with $F$ given by `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p`, with $F$ and $\mathrm{Finv}$ mutually inverse, and with $\mathrm{Fstar}\,z = p \cdot \mathrm{Finv}\,z$.
--
--   Diamond group (`pb`, `hpb`, `δ`, `hδ`): a unit $\mathrm{pb}$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$, and an endomorphism $\delta$ of $\mathrm{Pic}^0(\kappa,\overline{F})$ given by the action of $\mathrm{ofAlgAut}$ of `diamondActionModL κ (M/p) H' (CuspForm.gammaLift (M/p) pb)`.
--
--   Degeneracy group (`αpull`, `degPull`, `hpull`, `hpull_mul`, `hpullsp`): homomorphisms $\alpha_{\mathrm{pull}}\,i : J_{H'}(M/p) \to J_H(M)$ and morphisms $\mathrm{degPull}\,i$ from $\Lambda.f$ to $O.g$ over `base p`, such that $O.\mathtt{pts}(\alpha_{\mathrm{pull}}\,i\,x)$ is $\Lambda.\mathtt{pts}(x)$ followed by $\mathrm{degPull}\,i$; such that $\mathrm{degPull}\,i$ is compatible with the relative group laws on arbitrary bases; and such that for every section $x$ over `resPt A ≫ Λ.σA` the image under `GluedPic0.toPic0Pair O.ssFinset` of $O.\mathtt{ptsSp}^{-1}$ of ($x$ followed by $\mathrm{degPull}\,i$) is $(\Lambda.\mathtt{ptsSp}^{-1}x, \mathrm{Fstar}(\Lambda.\mathtt{ptsSp}^{-1}x))$ for $i = 0$ and $(\mathrm{Fstar}(\Lambda.\mathtt{ptsSp}^{-1}x), \delta(\Lambda.\mathtt{ptsSp}^{-1}x))$ for $i = 1$.
--
--   Atkin–Lehner group (`Wbar`, `wgen`, `hWbar`, `hwgen`): an endomorphism $\overline{W}$ of $J_H(M)$, a semilinear automorphism $w_{\mathrm{gen}}$ of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ with $\overline{W}x = w_{\mathrm{gen}} \cdot x$, and the geometric pin: whenever $y'$ read through `eeta`, `pullback.fst` and $\mathfrak{X}.w$ equals $y$ read through `eeta` and `pullback.fst`, then $\mathtt{pointEquivPlace}\,y' = w_{\mathrm{gen}} \cdot \mathtt{pointEquivPlace}\,y$.
--
--   Hecke relation (`S`, `hUPgen`): a set $S$ of natural numbers such that for all $x \in J_H(M)$, $\mathtt{genOpH}\,M\,H\,S$ of the generator $U_p$ applied to $x$, plus $\overline{W}x$, equals $\alpha_{\mathrm{pull}}\,1\,(O.\mathtt{degPts}\,0\,x)$.
--
--   Node shift (`σ`, `hσ`): a permutation $\sigma$ of $O.\mathtt{ssFinset}$ with the second coordinate of $\sigma n$ equal to the first coordinate of $n$.
--
--   Frobenius on places (`Φ`, `hΦ`, `hFdiv`): a permutation $\Phi$ of the places of $\overline{F}$ over $\kappa$ given by `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`, together with the compatibility: if a degree-zero divisor $D'$ equals `Finsupp.mapDomain Φ D`, then $F[D] = [D']$.
--
--   Level and character conditions (`hpM2`, `hHp`): $p^2 \nmid M$, and every unit $u$ of $\mathbb{Z}/M$ with trivial image in $(\mathbb{Z}/(M/p))^\times$ lies in $H$.
--
--   $q$-expansion pins (`θ`, `hθ`, `hwgenθ`, `αH`, `βH`, `hαint`, `hβint`, `hαq`, `hβq`, together with an instance giving principal divisors on `xHFunctionFieldBar M H`): a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of `xHFunctionFieldBar M H` such that whenever $f$ has the same Laurent expansion as an element $u$ of `xHFunctionFieldBar (M/p) H'`, the expansion of $\theta f$ is `qExpand` at $p$ of that of $u$, with $w_{\mathrm{gen}} = \mathrm{ofAlgAut}\,\theta$; and two $\overline{\mathbb{Q}}$-algebra maps $\alpha_H, \beta_H$ from `xHFunctionFieldBar (M/p) H'` to `xHFunctionFieldBar M H`, both integral, with $\alpha_H$ preserving Laurent expansions and $\beta_H$ sending the expansion of $u$ to `qExpand` at $p$ of it.
--
--   Divisor-level pins (`hpull1div`, `hdeg0div`): if $D_v$ is the pull-back `Divisor.pullbackAlong βH hβint` of a degree-zero divisor $D_w$ of `xHFunctionFieldBar (M/p) H'`, then $\alpha_{\mathrm{pull}}\,1\,[D_w] = [D_v]$; and if $D_w$ is the push-forward `Divisor.pushforwardAlong αH hαint` of a degree-zero divisor $D_v$, then $O.\mathtt{degPts}\,0\,[D_v] = [D_w]$.
--
--   Under these hypotheses the conclusion asserts: for every degree-zero divisor $D$ of $\overline{F}$ over $\kappa$ and every admissible gluing datum $x_1 \in$ `GluingData.admissible O.ssFinset`, if
--
--   (i) for every $s \in O.\mathtt{ssFinset}$ one has $D(s_1) = 0$ and $D(\Phi s_1) = 0$, where $s_1$ is the first coordinate of $s$;
--
--   (ii) the first component of $x_1$ is $p \cdot$ `Finsupp.mapDomain Φ.symm` $D$;
--
--   (iii) the second component of $x_1$ is $\mathrm{ofAlgAut}$ of `diamondActionModL κ (M/p) H' (CuspForm.gammaLift (M/p) pb)` acting on $D$;
--
--   (iv) the third component of $x_1$ is $0$;
--
--   then $O.\mathtt{ptsSp}^{-1}$ of the section obtained by composing $\Lambda.\mathtt{ptsSp}([D])$ with $\mathrm{degPull}\,1$ equals the glued class `GluedPic0.mk O.ssFinset x₁`.
--
--   This identifies the reduction at $p$ of the second degeneracy pull-back from level $(M/p, H')$ to level $(M,H)$, in the Deligne–Rapoport picture of the special fibre as two copies of the level-$(M/p)$ curve glued along the supersingular points: a degree-zero divisor class $[D]$ avoiding the crossings and their Frobenius translates pulls back to the glued class with components $p \cdot \Phi^{-1}_*D$ on the first copy, $\langle p \rangle_* D$ on the second, and trivial node datum. It feeds the construction of the level-data dictionary for $J_H(M)$ at $p$ and the Eichler–Shimura style relation between $U_p$, the diamond operator and Frobenius on the Tate module used in the ordinary case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_ptsSp_degPull_one_eq_mk_of_forall_apply_eq_zero_of_pullbackAlong.lean

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

theorem ModularCurve.JHNeronObjectAtP.ptsSp_symm_schemeHomOverComp_ptsSp_degPull_one_eq_mk_of_forall_apply_eq_zero_of_pullbackAlong
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

    (Φ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃ Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hΦ : ∀ v, Φ v = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v)
    (hFdiv : ∀ (D D' : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A))),
      (D' : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.mapDomain Φ (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) →
      F (Pic0.mk D) = Pic0.mk D')

    (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgenθ : wgen = SemilinearAut.ofAlgAut θ)
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (hαq : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβq : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hpull1div : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
      αpull 1 (Pic0.mk Dw) = Pic0.mk Dv)
    (hdeg0div : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
      O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    :
    ∀ (D : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (x₁ : ↥(GluingData.admissible O.ssFinset)),
      (∀ s ∈ O.ssFinset, (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) s.1 = 0 ∧
        (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (Φ s.1) = 0) →
      (x₁ : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (p : ℤ) • Finsupp.mapDomain Φ.symm (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) →
      (x₁ : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb)) • (D : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) →
      (x₁ : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0 →
      O.ptsSp.symm (schemeHomOverComp (Λ.ptsSp (Pic0.mk D)) (degPull 1)) = GluedPic0.mk O.ssFinset x₁ := by sorry
