-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords
-- name    : ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/24561c67-404a-5076-aecd-4d0453ab0a63
-- title:
--   Néron object for J_H(M) at p ∥ M with torus coordinates
-- statement:
--   Fix a prime $p$ and $M\ge 1$ together with a subgroup $H\le(\mathbb Z/M)^\times$, and write $H'=\mathtt{infSubgroup}\,p\,M\,H$ for the image of $H$ under the reduction $(\mathbb Z/M)^\times\to(\mathbb Z/(M/p))^\times$.
--
--   **Level hypotheses.** $p\mid M$ (`hpM`), $p^2\nmid M$ (`hpM2`), and `hHp`: every unit $u$ of $\mathbb Z/M$ with `ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1` lies in $H$, i.e. $H$ contains the kernel of reduction to $(\mathbb Z/(M/p))^\times$. Also $M/p\neq 0$, and `hj` asserts that the $q$-expansion `jqModC ℚ` of $j$ lies in the level-$\top$ $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`. Finally $\mathfrak X$ is a Deligne–Rapoport datum `XHDRModelAtP p M H hpM hj`: the two-chart integral model `X p (ΓM M H) hj` over `R p` with its structural morphism `toBase p (ΓM M H) hj`, the cusp section $\varepsilon_\infty$, the degeneracy morphisms $\pi,\pi_w$, the Atkin–Lehner isomorphism $w$, a curve model $\mathfrak X.\mathrm{Meta}$ over $\overline{\mathbb Q}$ of the function field `xHFunctionFieldBar M H` together with the identification $\mathfrak X.\mathrm{eeta}$ of its underlying scheme with the $\overline{\mathbb Q}$-fibre of the model, and the accompanying special-fibre data.
--
--   **Atkin–Lehner pin.** $\theta$ is an $\overline{\mathbb Q}$-algebra automorphism of `xHFunctionFieldBar M H` such that (`hθ`) whenever $f$ in that field and $u$ in `xHFunctionFieldBar (M / p) H'` have the same Laurent expansion, the expansion of $\theta f$ is `qExpand (AlgebraicClosure ℚ) p` applied to that of $u$, that is, is obtained by the substitution $q\mapsto q^p$; and (`hwgen`) for all $\overline{\mathbb Q}$-points $y,y'$ of $\mathfrak X.\mathrm{Meta}.C$ (sections of $\mathfrak X.\mathrm{Meta}.\mathrm{toBase}$), if $y'$ followed by $\mathfrak X.\mathrm{eeta}$, the first projection and $\mathfrak X.w.\mathrm{hom}$ agrees with $y$ followed by $\mathfrak X.\mathrm{eeta}$ and the first projection, then `𝔛.Meta.pointEquivPlace y'` is the translate of `𝔛.Meta.pointEquivPlace y` by the semilinear automorphism `SemilinearAut.ofAlgAut θ`.
--
--   **Place data.** $A$ is a valuation subring of $\overline{\mathbb Q}$ with `A.LiesOverPrime p` (that is, $p$ lies in `A.nonunits`), whose residue field $\kappa=\mathrm{ResidueField}\,A$ is algebraically closed of characteristic $p$, and $\rho : R\,p\to A$ is a ring homomorphism lifting the structural map, i.e. `A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)`.
--
--   **Conclusion.** There exist: level data $\Lambda$ of type `JHNeronObjectAtP.LevelData p M H hpM A` (a morphism $\sigma_A$ from $\operatorname{Spec} A$ to `base p` compatible with `genPt p`, a scheme $\Lambda.X$ with structural morphism $\Lambda.f$, a relative group law $\Lambda.L$, a bijection $\Lambda.\mathrm{pts}$ from $J_{H'}(M/p)=\mathrm{Pic}^0(\overline{\mathbb Q},\,$`xHFunctionFieldBar (M/p) H'`$)$ onto the points of $\Lambda.f$ over `genPt p`, and a bijection $\Lambda.\mathrm{ptsSp}$ from $\mathrm{Pic}^0(\kappa,\,$`Fbar p M H hpM κ`$)$ onto the points of $\Lambda.f$ over `resPt A ≫ Λ.σA`); an object $O$ of type `JHNeronObjectAtP p M H hpM A hA Λ` over it; representability data $hD$, $hDQ$; a separatedness witness for `baseChange (R p) (toBase p (ΓM M H) hj) ℚ`; morphisms $aj_{\mathbb Q}$, $k_{\mathbb Q}$, $\overline{aj}$ and a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathfrak X.\mathrm{Meta}.C$; two $\overline{\mathbb Q}$-algebra maps $\alpha_H,\beta_H$ from `xHFunctionFieldBar (M/p) H'` to `xHFunctionFieldBar M H` with integrality witnesses $h\alpha_{\mathrm{int}},h\beta_{\mathrm{int}}$, a witness that `xHFunctionFieldBar M H` has principal divisors, two additive maps $\alpha_{\mathrm{pull}}(i):J_{H'}(M/p)\to J_H(M)$ and two morphisms $\mathrm{degPull}(i)$ from $\Lambda.f$ to $O.g$ over `base p` ($i\in\{0,1\}$); a curve model $\mathrm{Meta}_0$ over $\overline{\mathbb Q}$ of `xHFunctionFieldBar (M/p) H'`, an isomorphism $\eta_0$ from its underlying scheme to the $\overline{\mathbb Q}$-fibre of `toBase p (ΓN p M H hpM) hj` and a morphism $\overline{aj}_0:\mathrm{Meta}_0.C\to\Lambda.X$; additive endomorphisms $F,F^{-1}_{\ }, F^{*},\delta$ of $\mathrm{Pic}^0(\kappa,$`Fbar p M H hpM κ`$)$ and a unit $p_b$ of $\mathbb Z/(M/p)$; and an isomorphism $B$ of the character lattice `characterLattice ↥O.ssFinset` with $\mathbb Z^{O.\mathrm{toricRank}}$, such that all of the following hold.
--
--   The designation attached to $O$ is the triple consisting of $O.G$, $O.g$ and the identity section of the relative group law $O.L$ at the identity of $\operatorname{Spec}(R\,p)$; the designation attached to $\Lambda$ is formed in the same way from $\Lambda.X$, $\Lambda.f$, $\Lambda.L$. Throughout, `algEquivZeroCut` denotes the subcondition on rigidified line bundles cutting out those that are fibrewise algebraically equivalent to zero, and `RepresentsRelSubPic` carries a Poincaré bundle satisfying the condition, the universal property, and triviality along the zero section.
--
--   (σ) $\Lambda.\sigma_A$ equals $\operatorname{Spec}$ of $\rho$.
--
--   (Pic$^0$ at level $\Gamma_N$) The designation of $\Lambda$ represents, nonemptily, the relative sub-Picard functor for `toBase p (ΓN p M H hpM) hj` rigidified along the section $\varepsilon_\infty$ followed by $\pi$, cut out by `algEquivZeroCut`. The datum $hD$ states the same for `toBase p (ΓM M H) hj` with $\varepsilon_\infty$ and the designation of $O$; thus $O.G$ and $\Lambda.X$ are the relative $\mathrm{Pic}^0$'s of the two Deligne–Rapoport models.
--
--   (generic fibre) $hDQ$ is the corresponding representability over $\mathbb Q$, for `baseChange (R p) (toBase p (ΓM M H) hj) ℚ` with section `sectionBaseChange ℚ 𝔛.εinf` and the base-changed designation; its Poincaré bundle is isomorphic (nonemptily) to the bundle obtained from $hD$'s Poincaré bundle by pulling back along the first projection of $O.g\times_{R p}\mathbb Q$ and applying `BaseChange.ofR`.
--
--   (Abel–Jacobi over $\mathbb Q$) The cusp section `sectionBaseChange ℚ 𝔛.εinf` followed by $aj_{\mathbb Q}$ is the zero section of the base-changed designation; and for every field $K$, every morphism $t:\operatorname{Spec}K\to\operatorname{Spec}\mathbb Q$ and every $K$-point $x$ of the base-changed curve, the pullback of the Poincaré bundle of $hDQ$ along $x$ followed by $aj_{\mathbb Q}$ is isomorphic to the tensor product of the line bundle of the relative effective Cartier divisor `RelEffCartierDiv.ofPoint` at $x$ with the ideal module of the one at $t$ followed by the cusp section, i.e. $aj_{\mathbb Q}$ classifies the class of $[x]-[\varepsilon_\infty]$.
--
--   (comparison morphism) $k_{\mathbb Q}$ followed by the first projection is the first projection, and followed by the second projection is the second projection followed by $\operatorname{Spec}$ of $\mathbb Q\to\overline{\mathbb Q}$.
--
--   ($\overline{aj}$) $\overline{aj}$ equals $\mathfrak X.\mathrm{eeta}$ followed by $k_{\mathbb Q}$, by $aj_{\mathbb Q}$ and by the first projection of $O.g\times_{R p}\mathbb Q$; and $\overline{aj}$ followed by $O.g$ is $\mathfrak X.\mathrm{Meta}.\mathrm{toBase}$ followed by `genPt p`. The point $\bar\varepsilon$ is the cusp: read in the model through $\mathfrak X.\mathrm{eeta}$ and the first projection it is `genPt p` followed by $\varepsilon_\infty$, and $\bar\varepsilon$ followed by $\overline{aj}$ is `genPt p` followed by the identity section of $O.L$.
--
--   (additivity) $O.\mathrm{pts}$ is additive for the relative group law induced by the representability datum $hD$ through `algEquivZeroGroupCut`: $O.\mathrm{pts}(x+y)$ is the product of $O.\mathrm{pts}\,x$ and $O.\mathrm{pts}\,y$.
--
--   (points dictionary in characteristic zero) For all $\overline{\mathbb Q}$-points $x,s$ of $\mathfrak X.\mathrm{Meta}.C$ with $s$ lying over the cusp, there is a degree-zero divisor $D_v$ equal to $\mathrm{single}(\mathrm{place}\,x)-\mathrm{single}(\mathrm{place}\,s)$, where places are taken via `𝔛.Meta.pointEquivPlace`, such that the point $O.\mathrm{pts}(\mathrm{Pic}^0\text{-class of }D_v)$ is $x$ followed by $\overline{aj}$.
--
--   (degeneracy maps on $q$-expansions) For every $u$ in `xHFunctionFieldBar (M/p) H'`, the Laurent expansion of $\alpha_H u$ equals that of $u$, while that of $\beta_H u$ is `qExpand (AlgebraicClosure ℚ) p` of the expansion of $u$.
--
--   (push-forward and pull-back dictionaries) If a degree-zero divisor $D_w$ at level $(M/p,H')$ is `Divisor.pushforwardAlong αH hαint` of a degree-zero divisor $D_v$ at level $(M,H)$, then $O.\mathrm{degPts}\,0$ sends the class of $D_v$ to the class of $D_w$; the same with $\beta_H$ and $O.\mathrm{degPts}\,1$. Dually, if $D_v$ is `Divisor.pullbackAlong αH hαint` of $D_w$, then $\alpha_{\mathrm{pull}}0$ sends the class of $D_w$ to the class of $D_v$; likewise with $\beta_H$ and $\alpha_{\mathrm{pull}}1$.
--
--   (degPull) For each $i$ and each $x\in J_{H'}(M/p)$, the point $O.\mathrm{pts}(\alpha_{\mathrm{pull}}i\,x)$ equals $\Lambda.\mathrm{pts}\,x$ followed by $\mathrm{degPull}(i)$; and $\mathrm{degPull}(i)$ is a homomorphism of relative group laws: for every scheme $T$, every $s:T\to$ `base p` and all points $x,y$ over $s$, the composite of $\Lambda.L.\mathrm{mul}\,s\,x\,y$ with $\mathrm{degPull}(i)$ equals $O.L.\mathrm{mul}\,s$ of the two composites.
--
--   (reduction dictionary, glued form) For each $i\in\{0,1\}$ and each collection of data consisting of: $\overline{\mathbb Q}$-points $y_1,y_2$ of $\mathfrak X.\mathrm{Meta}.C$; points $u_1,u_2$ of the model over $\operatorname{Spec}\rho$ whose composites with `barPt A` agree with $y_1,y_2$ read through $\mathfrak X.\mathrm{eeta}$ and the first projection and whose images lie in $\mathfrak X.\mathrm{smoothLocus}$; residue-field points $u_{\kappa,1},u_{\kappa,2}$ of the fibre of `toBase p (ΓM M H) hj` along `residue A ∘ ρ` reducing $u_1,u_2$ and sectioning the second projection; closed points $P_1,P_2$ of the special-fibre curve model `𝔛.Mfib A hA ρ hρ` whose images under $\mathfrak X.\mathrm{efib}$ followed by `𝔛.comp A hA ρ hρ i` are the closed points of $u_{\kappa,1},u_{\kappa,2}$; a degree-zero divisor $D_v=\mathrm{single}(\mathrm{place}\,y_1)-\mathrm{single}(\mathrm{place}\,y_2)$; and an admissible gluing datum $x$ for `O.ssFinset` whose first divisor component is $\mathrm{single}(\mathrm{place}\,P_1)-\mathrm{single}(\mathrm{place}\,P_2)$ if $i=0$ and $0$ otherwise, whose second divisor component is that difference if $i=1$ and $0$ otherwise, and whose unit component is $0$ — there exists a point $s$ of $O.g$ over $\Lambda.\sigma_A$ with $O.\mathrm{pts}(\text{class of }D_v)$ equal to `barPt A` followed by $s$, and with $O.\mathrm{ptsSp}^{-1}$ of the restriction of $s$ along `resPt A` equal to the class `GluedPic0.mk O.ssFinset x`.
--
--   (reduction dictionary at level $\Gamma_N$) For each $i$ and each collection of data consisting of $\overline{\mathbb Q}$-points $y_1,y_2$, points $u_1,u_2$ over $\operatorname{Spec}\rho$ compatible with them, residue-field fibre points $u_{\kappa,1},u_{\kappa,2}$ as above, closed points $Q_1,Q_2$ of `𝔛.Mfib A hA ρ hρ` whose images under $\mathfrak X.\mathrm{efib}$ are the closed points of $u_{\kappa,1},u_{\kappa,2}$ transported by the fibre map of $\pi$ (for $i=0$) or $\pi_w$ (for $i=1$), a degree-zero divisor $D_v=\mathrm{single}(\mathrm{place}\,y_1)-\mathrm{single}(\mathrm{place}\,y_2)$ and a degree-zero divisor $D_w=\mathrm{single}(\mathrm{place}\,Q_1)-\mathrm{single}(\mathrm{place}\,Q_2)$ over $\kappa$ — there exists a point $s_0$ of $\Lambda.f$ over $\Lambda.\sigma_A$ with $\Lambda.\mathrm{pts}(O.\mathrm{degPts}\,i(\text{class of }D_v))$ equal to `barPt A` followed by $s_0$, and $\Lambda.\mathrm{ptsSp}^{-1}$ of its restriction along `resPt A` equal to the class of $D_w$.
--
--   (diamonds on the special fibre) For every unit $e$ of $\mathbb Z/(M/p)$ and every closed point $P$ of `(𝔛.Mfib A hA ρ hρ).C`, the point obtained by transporting $P$ through $\mathfrak X.\mathrm{efib}$, the fibre map of `overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)` and the inverse of $\mathfrak X.\mathrm{efib}$ is again a closed point, and its place is the translate of the place of $P$ by the semilinear automorphism attached to `diamondActionModL κ (M/p) H' (CuspForm.gammaLift (M/p) e)`.
--
--   (inertia) For every $m>0$, every $\sigma$ in `A.inertiaSubgroupIn ℚ` and every $m$-torsion class $x$ in $\mathrm{Pic}^0(\overline{\mathbb Q},$`xHFunctionFieldBar M H`$)$, the difference $\sigma\cdot x-x$ lies in $O.\mathrm{finPts}\,m$, the subgroup generated by the $m$-torsion classes whose points extend to the place $A$.
--
--   (level-$\Gamma_N$ uniformisation) $\eta_0$ followed by the second projection is $\mathrm{Meta}_0.\mathrm{toBase}$. For $\overline{\mathbb Q}$-points $y$ of $\mathfrak X.\mathrm{Meta}.C$ and $y_0$ of $\mathrm{Meta}_0.C$: if $y_0$ read through $\eta_0$ and the first projection agrees with $y$ read through $\mathfrak X.\mathrm{eeta}$, the first projection and $\pi$, then the place of $y_0$ is `Place.restrictAlong αH hαint` of the place of $y$; if instead the comparison is made through $\mathfrak X.w.\mathrm{hom}$ followed by $\pi$, the place of $y_0$ is `Place.restrictAlong βH hβint` of the place of $y$. Moreover $\overline{aj}_0$ followed by $\Lambda.f$ is $\mathrm{Meta}_0.\mathrm{toBase}$ followed by `genPt p`, and for all $\overline{\mathbb Q}$-points $x_0,s_0$ of $\mathrm{Meta}_0.C$ with $s_0$ lying over the cusp (read through $\eta_0$, the first projection, and equal to `genPt p` followed by $\varepsilon_\infty$ and $\pi$) there is a degree-zero divisor $D_{v_0}=\mathrm{single}(\mathrm{place}\,x_0)-\mathrm{single}(\mathrm{place}\,s_0)$ with $\Lambda.\mathrm{pts}$ of its class equal to $x_0$ followed by $\overline{aj}_0$.
--
--   (Frobenius and diamond in characteristic $p$) $F$ is the map `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p`; $F$ and $F^{-1}_{\ }$ are mutually inverse; $F^{*}z=p\cdot F^{-1}_{\ }z$ for all $z$; the unit $p_b$ reduces to $p$ in $\mathbb Z/(M/p)$; and $\delta$ is the action of the semilinear automorphism attached to `diamondActionModL κ (M/p) H' (CuspForm.gammaLift (M/p) pb)`.
--
--   (degeneracies in glued coordinates) For each $i$ and each point $x$ of $\Lambda.f$ over `resPt A ≫ Λ.σA`, the image under `GluedPic0.toPic0Pair O.ssFinset` of $O.\mathrm{ptsSp}^{-1}$ of the composite of $x$ with $\mathrm{degPull}(i)$ is the pair $(\Lambda.\mathrm{ptsSp}^{-1}x,\;F^{*}(\Lambda.\mathrm{ptsSp}^{-1}x))$ when $i=0$, and $(F^{*}(\Lambda.\mathrm{ptsSp}^{-1}x),\;\delta(\Lambda.\mathrm{ptsSp}^{-1}x))$ when $i=1$.
--
--   (torus coordinates) For every $\kappa$-algebra homomorphism $\chi$ from `torusCoord κ O.toricRank`, the group algebra $\kappa[\mathbb Z^{O.\mathrm{toricRank}}]$, to $\kappa$, and every family $w$ of elements of $\mathrm{Additive}\,\kappa^\times$ indexed by `O.ssFinset`: the composite of the torus point `torusPt κ O.toricRank χ` with $O.\mathrm{torusFibre}$ equals the fibre point of $O.\mathrm{ptsSp}$ applied to the node class `GluedPic0.nodeUnit O.ssFinset w` if and only if, for every $a$ in the character lattice `characterLattice ↥O.ssFinset`, the product over $s$ of the multiplicative avatars of $w(s)$ raised to the power $a(s)$, viewed in $\kappa$, equals $\chi$ of the monomial `AddMonoidAlgebra.single (B a) 1`.
--
--   This is the existence statement, at a prime $p$ exactly dividing the level $M$, for the Néron object of $J_H(M)$ over $\mathbb Z_{(p)}$ realised as the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model of $X_H(M)$, packaged together with the complete dictionary relating its points to divisor classes in characteristic zero and on the special fibre, the behaviour of the two degeneracy maps, the Frobenius and diamond operators, the inertia action, and the toric coordinates on the special fibre. It is the geometric input for the local analysis at $p\parallel M$ used in level lowering, and is cited by the statements about the inertia action on the Tate module of $J_H(M)$ and about the relation between diamond operators and $U_p$ at a Frobenius place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups
set_option maxHeartbeats 400000 in

theorem ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    ∃ (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)

      (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

      (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
      (_ : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
      (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
      (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
      (ajbar : 𝔛.Meta.C ⟶ O.G)
      (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})

      (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
      (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
      (_ : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
      (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
      (degPull : Fin 2 → SchemeHomOver Λ.f O.g)

      (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
      (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
      (_ : IsIso eeta₀)
      (ajbar₀ : Meta₀.C ⟶ Λ.X)

      (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
        Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
      (pb : (ZMod (M / p))ˣ)
      (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
        Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))

      (B : characterLattice ↥O.ssFinset ≃+ (Fin O.toricRank → ℤ)),

      Λ.σA = Spec.map (CommRingCat.ofHom ρ) ∧

      Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))) ∧

      Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L) ∧

      (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection ∧

      (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule)) ∧

      kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p) ∧
      kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧

      ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ) ∧
      ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p ∧
      εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ∧
      εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1 ∧

      (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)) ∧

      (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
            Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
          (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar) ∧

      (∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))) ∧
      (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) ∧

      (∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
        (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw) ∧
      (∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
        (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong βH hβint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 1 (Pic0.mk Dv) = Pic0.mk Dw) ∧

      (∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Divisor.pullbackAlong αH hαint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 0 (Pic0.mk Dw) = Pic0.mk Dv) ∧
      (∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) →
        αpull 1 (Pic0.mk Dw) = Pic0.mk Dv) ∧

      (∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
        (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1) ∧

      (∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
        schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
          O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i))) ∧

      (∀ (i : Fin 2)
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
        O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x) ∧

      (∀ (i : Fin 2)
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
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw) ∧

      (∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P) ∧

      (∀ (m : ℕ), 0 < m → ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m, σ • x - x ∈ O.finPts m) ∧

      eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase ∧
      (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
        y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 →
        Meta₀.pointEquivPlace y₀ = Place.restrictAlong αH hαint (𝔛.Meta.pointEquivPlace y)) ∧
      (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
        y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom ≫ 𝔛.π.1 →
        Meta₀.pointEquivPlace y₀ = Place.restrictAlong βH hβint (𝔛.Meta.pointEquivPlace y)) ∧
      ajbar₀ ≫ Λ.f = Meta₀.toBase ≫ genPt p ∧
      (∀ (x₀ s₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
        s₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1 →
        ∃ Dv₀ : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
          (Dv₀ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
            Finsupp.single (Meta₀.pointEquivPlace x₀) 1 - Finsupp.single (Meta₀.pointEquivPlace s₀) 1 ∧
          (Λ.pts (Pic0.mk Dv₀)).1 = x₀.1 ≫ ajbar₀) ∧

      (∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z) ∧
      (F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _) ∧
      (∀ z, Fstar z = (p : ℤ) • Finv z) ∧
      ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)) ∧
      (∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) pb)) • z) ∧
      (∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
        GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
          if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
          else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x))) ∧

      (∀ (χ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)
          (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ),
        NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank χ) O.torusFibre =
            toFibrePt (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w)) ↔
          ∀ a : characterLattice ↥O.ssFinset,
            ((∏ s, Additive.toMul (w s) ^ (a : ↥O.ssFinset → ℤ) s : (ResidueField ↥A)ˣ) : ResidueField ↥A) =
              χ (AddMonoidAlgebra.single (B a) 1)) := by sorry
