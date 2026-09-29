-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_hecke_U_mk_eq_mk_frobPullback_and_exists_mk_eq_of_snd_eq_zero
-- name    : ModularCurve.JHNeronObjectAtP.ptsSp_symm_hecke_U_mk_eq_mk_frobPullback_and_exists_mk_eq_of_snd_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/afef7355-b81e-58e7-a630-74936393231e
-- title:
--   Uₚ as Frobenius pull-back on glued special-fibre classes
-- statement:
--   Fix a prime $p$ and a natural number $M$ with $p \mid M$ and $M/p$ nonzero, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and the hypothesis `hj` that the $q$-expansion $j$-series `jqModC ℚ` lies in the function field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be a Deligne–Rapoport-type model `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over the base ring $R_p$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its set of nonunits (`A.LiesOverPrime p`), with residue field $\kappa =$ `ResidueField ↥A` of characteristic $p$ and algebraically closed. Let $\Lambda$ be a `LevelData p M H hpM A` — supplying a structure morphism $\Lambda.\sigma_A$ from $\operatorname{Spec} A$ to the base, a scheme $\Lambda.f$ over the base with a relative group law, a bijection $\Lambda.\mathrm{pts}$ between $J_H(M/p)$ at level `infSubgroup p M H hpM` and the generic points of $\Lambda.f$, and a bijection $\Lambda.\mathrm{ptsSp}$ between $\mathrm{Pic}^0(\bar F)$, $\bar F =$ `Fbar p M H hpM κ` $=$ `qExpFunctionFieldC κ (ΓN p M H hpM)`, and the $\kappa$-points of $\Lambda.f$ — and let $O$ be a `JHNeronObjectAtP p M H hpM A hA Λ`, i.e. a Néron-model object $O.g$ over the base with group law, with $O.\mathrm{pts} : J_H(M) \simeq$ generic points, with Hecke endomorphisms $O.\mathrm{hecke}$, with a finite set $O.\mathrm{ssFinset}$ of pairs of places of $\bar F$ (the glueing data indexing the nodes) and a bijection $O.\mathrm{ptsSp}$ between `GluedPic0 κ (Fbar …) O.ssFinset` and the $\kappa$-points of $O.g$. Finally let $\rho : R_p \to A$ satisfy `A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)` and $\Lambda.\sigma_A = \operatorname{Spec}(\rho)$.
--
--   Here `GluingData κ 𝔽 S` is the product `Divisor κ 𝔽 × Divisor κ 𝔽 × (↥S → Additive κˣ)`, and `GluingData.admissible S` cuts out those triples whose first two divisors have degree zero and which vanish at the nodes in the sense that $x_1(s_1) = 0$ and $x_{2,1}(s_2) = 0$ for every $s \in S$; `GluedPic0` is the quotient of the admissible data by the glued principal data, and `GluedPic0.toPic0Pair` sends a class to the pair of $\mathrm{Pic}^0$-classes of its two divisor coordinates.
--
--   The hypotheses fall into the following groups.
--
--   Reduction dictionary for $O$ (`hsp`, summarised here). For each $i \in \{0,1\}$: given two $\overline{\mathbb{Q}}$-points $y_1, y_2$ of the generic curve model $\mathfrak{X}.\mathrm{Meta}$, $A$-valued points $u_1, u_2$ of the integral model over $\operatorname{Spec}(\rho)$ whose base changes along `barPt A` are $y_1, y_2$ composed with $\mathfrak{X}.\mathrm{eeta}$ followed by the first pullback projection, whose topological images lie in $\mathfrak{X}.\mathrm{smoothLocus}$; given $\kappa$-points $u_{\kappa,1}, u_{\kappa,2}$ of the fibre which are the reductions of $u_1, u_2$ (first projection equal to $\operatorname{Spec}(\text{residue})$ followed by $u_j$, second projection the identity); given closed points $P_1, P_2$ of the special-fibre curve model $\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho$ whose images under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\,i$ are the closed points of $u_{\kappa,1}, u_{\kappa,2}$; given a degree-zero divisor $D_v$ on $\overline{\mathbb{Q}}$ equal to $[y_1] - [y_2]$ under `pointEquivPlace`; and given an admissible glueing datum $x$ whose first coordinate is $[P_1] - [P_2]$ if $i = 0$ and $0$ otherwise, whose second divisor coordinate is $[P_1] - [P_2]$ if $i = 1$ and $0$ otherwise, and whose unit coordinate is $0$ — then there is an $A$-point $s$ of $O.g$ over $\Lambda.\sigma_A$ with $(O.\mathrm{pts}\,[D_v])_1 = \mathtt{barPt }A \cdot s_1$ and with $O.\mathrm{ptsSp}^{-1}$ of the precomposition of $s$ with `resPt A` equal to the class of $x$.
--
--   Reduction dictionary for $\Lambda$ (`hspΛ`, summarised here). The same data, without the smooth-locus conditions, with closed points $Q_1, Q_2$ of the special-fibre model whose images under $\mathfrak{X}.\mathrm{efib}$ are the closed points of $u_{\kappa,j}$ composed with the fibre map of $\mathfrak{X}.\pi$ (if $i = 0$) or $\mathfrak{X}.\pi_w$ (if $i = 1$), with $D_v = [y_1] - [y_2]$ and $D_w = [Q_1] - [Q_2]$, yields an $A$-point $s_0$ of $\Lambda.f$ with $(\Lambda.\mathrm{pts}(O.\mathrm{degPts}\,i\,[D_v]))_1 = \mathtt{barPt }A \cdot (s_0)_1$ and $\Lambda.\mathrm{ptsSp}^{-1}$ of its reduction equal to $[D_w]$.
--
--   Diamond operators on the special fibre (`hdia0`). For every unit $e$ of $\mathbb{Z}/(M/p)$ and every closed point $P$ of the special-fibre model, the point obtained by transporting $P$ through $\mathfrak{X}.\mathrm{efib}$, the fibre map of the automorphism $\mathfrak{X}.\mathrm{dia0}\,e$ and the inverse of $\mathfrak{X}.\mathrm{efib}$ is again closed, and its place is the image of the place of $P$ under the semilinear automorphism attached to `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` applied to [`CuspForm.gammaLift (M/p) e`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36).
--
--   Frobenius data on $\mathrm{Pic}^0$ ($F$, $F^{-1}$, $F^{*}$ with `hF`, `hFinv`, `hFstar`). Three endomorphisms of $\mathrm{Pic}^0(\kappa, \bar F)$ are given: $F$ is `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p`, $F$ and `Finv` are mutually inverse, and `Fstar` is $p$ times `Finv`.
--
--   Diamond datum ($pb$, `hpb`, $\delta$, `hδ`). A unit $pb$ of $\mathbb{Z}/(M/p)$ reducing to $p$, and the endomorphism $\delta$ of $\mathrm{Pic}^0$ given by the action of the semilinear automorphism attached to `diamondActionModL` applied to [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36).
--
--   Degeneracy data ($\alpha_{\mathrm{pull}}$, $\deg_{\mathrm{Pull}}$, `hpull`, `hpull_mul`, `hpullsp`). For $i \in \{0,1\}$, homomorphisms $\alpha_{\mathrm{pull}}\,i : J_H(M/p) \to J_H(M)$ and morphisms $\deg_{\mathrm{Pull}}\,i$ from $\Lambda.f$ to $O.g$ over the base, such that on generic points $(O.\mathrm{pts}(\alpha_{\mathrm{pull}}\,i\,x))_1$ is $(\Lambda.\mathrm{pts}\,x)_1$ followed by $\deg_{\mathrm{Pull}}\,i$, such that each $\deg_{\mathrm{Pull}}\,i$ is additive for the two relative group laws on points over an arbitrary base scheme, and such that on $\kappa$-points `toPic0Pair` of $O.\mathrm{ptsSp}^{-1}$ of the composite with $\deg_{\mathrm{Pull}}\,i$ is $(\Lambda.\mathrm{ptsSp}^{-1}x,\ F^{*}\Lambda.\mathrm{ptsSp}^{-1}x)$ for $i = 0$ and $(F^{*}\Lambda.\mathrm{ptsSp}^{-1}x,\ \delta\,\Lambda.\mathrm{ptsSp}^{-1}x)$ for $i = 1$.
--
--   Atkin–Lehner datum ($\bar W$, `wgen`, `hWbar`, `hwgen`). An endomorphism $\bar W$ of $J_H(M)$ given by the action of a semilinear automorphism `wgen` of $\overline{\mathbb{Q}}$-function field `xHFunctionFieldBar M H`, compatible with $\mathfrak{X}.w$ in the sense that whenever $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, the first projection and $\mathfrak{X}.w$ equals $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection, the place of $y'$ is `wgen` applied to the place of $y$.
--
--   Generic Hecke identity ($S$, `hUPgen`). For a set of primes $S$ and every $x \in J_H(M)$, $\mathrm{genOpH}\,M\,H\,S\,(U_p)\,x + \bar W x = \alpha_{\mathrm{pull}}\,1\,(O.\mathrm{degPts}\,0\,x)$.
--
--   Node shift ($\sigma$, `hσ`). A permutation $\sigma$ of $O.\mathrm{ssFinset}$ with $(\sigma n)_2 = n_1$ for every $n$.
--
--   Frobenius on places and its effect on classes ($\Phi$, `hΦ`, `hFdiv`). A bijection $\Phi$ of the places of $\bar F$ over $\kappa$ equal to `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`, and the compatibility that $F[D] = [D']$ whenever $D'$ is the push-forward `Finsupp.mapDomain Φ` of $D$ on degree-zero divisors.
--
--   Glued-level bridge for the second degeneracy map (`hpull1sp`). For every degree-zero divisor $D$ on $\bar F$ and every admissible glueing datum $x_1$: if $D$ vanishes at $s_1$ and at $\Phi(s_1)$ for every $s \in O.\mathrm{ssFinset}$, if the first coordinate of $x_1$ is $p \cdot$ `Finsupp.mapDomain Φ.symm` $D$, if the second divisor coordinate of $x_1$ is the image of $D$ under the semilinear automorphism attached to `diamondActionModL` applied to [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36), and if the unit coordinate of $x_1$ is $0$, then $O.\mathrm{ptsSp}^{-1}$ of the composite of $\Lambda.\mathrm{ptsSp}[D]$ with $\deg_{\mathrm{Pull}}\,1$ is the class of $x_1$.
--
--   The conclusion is a conjunction of two assertions.
--
--   First: for all admissible glueing data $x$ and $x'$, if the second divisor coordinate of $x$ vanishes, if the first divisor coordinate of $x$ vanishes at $\Phi(s_1)$ for every $s \in O.\mathrm{ssFinset}$, if the first coordinate of $x'$ equals $p \cdot$ `Finsupp.mapDomain Φ.symm` of the first coordinate of $x$, if the second divisor coordinate of $x'$ vanishes, and if the unit coordinate of $x'$ is the unit coordinate of $x$ precomposed with $\sigma$, then $O.\mathrm{ptsSp}^{-1}$ of the composite of $O.\mathrm{ptsSp}$ of the class of $x$ with the Hecke endomorphism $O.\mathrm{hecke}\,S\,(U_p)$ equals the class of $x'$.
--
--   Second: for every class $\xi$ in `GluedPic0 κ (Fbar p M H hpM κ) O.ssFinset` whose second `toPic0Pair` component vanishes, there is an admissible glueing datum $x$ whose second divisor coordinate vanishes, whose first divisor coordinate vanishes at $\Phi(s_1)$ for every $s \in O.\mathrm{ssFinset}$, and whose class is $\xi$.
--
--   This is the computation of the Hecke operator $U_p$ on the special fibre of the Néron model of $J_H(M)$ at a prime $p$ exactly dividing the level, in the glued (Deligne–Rapoport) description of that fibre: on glueing data with vanishing second divisor coordinate and divisor support away from the Frobenius translates of the nodes, $U_p$ multiplies the divisor by $p$ and pulls it back along Frobenius while shifting the unit coordinate by the node permutation, and every class with vanishing second abelian-quotient component admits such a representative. It is used in the construction of the relative Frobenius factorisation of $U_p$ on the Néron model and, through it, in the descent statements for the Raynaud quotient of the finite points of the Néron object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_hecke_U_mk_eq_mk_frobPullback_and_exists_mk_eq_of_snd_eq_zero.lean

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

theorem ModularCurve.JHNeronObjectAtP.ptsSp_symm_hecke_U_mk_eq_mk_frobPullback_and_exists_mk_eq_of_snd_eq_zero
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
    :
    (∀ (x x' : ↥(GluingData.admissible O.ssFinset)),

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
        GluedPic0.mk O.ssFinset x = ξ) := by sorry
