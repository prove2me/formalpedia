-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_idempotent_pairing_corner_adjointCorner_perfect_galois_radical_ncard_toric_cyclotomic_eq_of_abelJacobiPin_of_levelData_of_algEquiv
-- name    : ModularCurve.JHNeronObjectAtP.exists_idempotent_pairing_corner_adjointCorner_perfect_galois_radical_ncard_toric_cyclotomic_eq_of_abelJacobiPin_of_levelData_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/a2dec545-1bc8-5ec1-805f-759ff6388dc3
-- title:
--   Idempotent and μₚ-pairing between corner and adjoint corner
-- statement:
--   Throughout, $\bar{\mathbb{Q}}$ denotes `AlgebraicClosure ℚ`, $J =$ `JH M H` is the degree-zero divisor class group $\mathrm{Pic}^0$ of the function field `xHFunctionFieldBar M H` of the modular curve $X_H$ of level $M$ over $\bar{\mathbb{Q}}$, and $T_pJ =$ [`TateModule p J`](def/EllipticCurve_TateModule.html#L15) is the group of sequences $(x_n)_{n\ge 0}$ in $J$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, on which [`TateModule.proj p J 1`](def/EllipticCurve_TateModule.html#L122) is evaluation at the index $1$ (so its image lies in $J[p]$).
--
--   The arithmetic data are: a prime $p$ with $p \neq 2$, a level $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ which by `hHp` contains every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is trivial, a set of primes $S$, and the hypothesis `hin`, which is `HeckeDiamondInputsHAll M H`: for every prime $\ell$ the inputs `HeckeInputsHAlong` over $\bar{\mathbb{Q}}$ at level $(M,H,\ell)$ hold, and for every $d \in (\mathbb{Z}/M)^\times$ there is a $\bar{\mathbb{Q}}$-algebra automorphism of `xHFunctionFieldBar M H` satisfying `IsDiamondAutHBar M H d`.
--
--   The Hecke data are: a commutative ring $\mathbb{T}$ which is a $\mathbb{Z}_p$-algebra acting on $T_pJ$ compatibly with the $\mathbb{Z}_p$-action, faithfully by `hfaith`; a map `op` from the generators [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) to $\mathbb{T}$ which by `hop` acts on $T_pJ$ as the operator `tateGenOpH M H S p` of the corresponding generator, and which by `hgen` generates $\mathbb{T}$ as a $\mathbb{Z}_p$-algebra; an idempotent splitting `S'` of $\mathbb{T}$, that is, finitely many elements $e_i$ forming a complete orthogonal family of idempotents together with maximal ideals $\mathfrak{m}_i$ exhausting all maximal ideals and satisfying $e_i \in \mathfrak{m}_j \iff i \neq j$; an index $i_0$; and `hord`, which asserts $\mathrm{op}(U_p) \notin \mathfrak{m}_{i_0}$ for the generator $U_p$ attached to $p \mid M$.
--
--   The geometric data at $p$ are: a valuation subring $\mathfrak{P}$ of $\bar{\mathbb{Q}}$ lying over $p$ (in the sense that $p$ lies in the non-units of $\mathfrak{P}$), with residue field of characteristic $p$ and algebraically closed; the hypothesis `hj` that `jqModC ℚ` lies in the $q$-expansion function field of level $\mathrm{SL}_2(\mathbb{Z})$; an integral model datum $\mathfrak{X} =$ `XHDRModelAtP p M H hpM hj` over $R_p =$ `ratLocalizedAt p`, carrying in particular the geometric curve model `𝔛.Meta` of `xHFunctionFieldBar M H` with its chart comparison `𝔛.eeta`; a level datum $\Lambda$ at $\mathfrak{P}$ for the level $M/p$ group `JH (M / p) (infSubgroup p M H hpM)` (a section $\sigma_A$, a scheme $\Lambda.X$ over the base with a relative group law, and parametrisations of its generic and special points); the hypothesis `hΛ` that $\Lambda.f$ satisfies `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, and carrying a relative group law); and a Néron object $O =$ `JHNeronObjectAtP p M H hpM Pl hPl Λ` for $J$ at $\mathfrak{P}$, with its scheme $O.G$ over the base, group law $O.L$, point parametrisation $O.\mathrm{pts}$, Hecke correspondences, toric rank, and the subgroups `O.finPts m` and `O.toricPts m` of $J$.
--
--   The Abel–Jacobi pinning hypotheses `hD`, `hDQ`, `hsep`, `ajQ`, `kQ`, `ajbar`, `εbar`, `hpoinc`, `hajQε`, `hajQ`, `hkQ₁`, `hkQ₂`, `hajbar`, `hajbar_over`, `hεbar`, `hεbar_aj`, `hpts_law`, `hAJ` (summarised here) state: that the designation with total space $O.G$, structure morphism $O.g$ and zero section the unit of $O.L$ represents, over $R_p$ and over $\mathbb{Q}$, the rigidified relative Picard functor cut out by fibrewise algebraic equivalence to zero, for the model of $X_H$ over $R_p$ with its section `𝔛.εinf`; that the base-changed curve over $\mathbb{Q}$ is separated; that `ajQ` is a morphism over the base from that curve to the base-changed Picard scheme, `kQ` a comparison morphism between the two pullbacks of the model along the geometric and the rational point of the base, compatible with both projections by `hkQ₁` and `hkQ₂`; that the Poincaré bundle over $\mathbb{Q}$ agrees with the base change of the one over $R_p$ (`hpoinc`); that `ajQ` carries the section to the zero section (`hajQε`) and that for every field $K$ and every $K$-point $x$ the pullback of the Poincaré bundle along $x$ followed by `ajQ` is the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of the base point (`hajQ`), so that `ajQ` is an Abel–Jacobi morphism; that `ajbar` is the resulting morphism from the geometric curve model to $O.G$ (`hajbar`), lying over the generic point (`hajbar_over`); that `εbar` is a base point of the geometric curve model compatible with `𝔛.εinf` (`hεbar`) and sent by `ajbar` to the unit section (`hεbar_aj`); that $O.\mathrm{pts}$ is additive for the relative group law supplied by `hD` (`hpts_law`); and that for any geometric points $x,s$ of the curve model with $s$ compatible with `𝔛.εinf` there is a degree-zero divisor equal to $[x]-[s]$ whose class has $O.\mathrm{pts}$ given by $x$ followed by `ajbar` (`hAJ`). The hypothesis `hrepΛ` asserts that the corresponding representability statement holds at level $\Gamma_N(p,M,H)$ for the designation built from $\Lambda.X$, $\Lambda.f$ and the unit of $\Lambda.L$.
--
--   The inertia ring data are: a commutative domain $R$ which is Henselian local with algebraically closed residue field, together with a faithful $R$-algebra structure on $\bar{\mathbb{Q}}$ whose structure map lands in $\mathfrak{P}$ (`hRA`), such that $R$ is a discrete valuation ring (`hRdvr`) in which $p$ is irreducible (`hRirr`), such that an element of $\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ lies in `Pl.inertiaSubgroupIn ℚ` exactly when it fixes the image of $R$ pointwise (`hRfix`), and such that every element of $\mathfrak{P}$ fixed by that inertia subgroup lies in the image of $R$ (`hRmax`).
--
--   The finite-part layer consists of a $p$-divisible group $\mathcal{G}$ over $R$ of height $h$ (a system of finite free Hopf algebras `𝒢.level v` of rank $p^{vh}$ with surjective transitions), an additive map $\Delta$ from $\mathcal{G}(\bar{\mathbb{Q}})$ to $J$, and a $\mathbb{Z}_p$-linear map $e$ from $T_p\mathcal{G}(\bar{\mathbb{Q}})$ to $T_pJ$, subject to: injectivity of $\Delta$ (`hΔinj`); the identification `hΔlev` of `O.finPts (p ^ v)` with the image under $\Delta$ of the level-$v$ points; Galois equivariance of $\Delta$ for automorphisms of $\bar{\mathbb{Q}}$ over $\mathbb{Q}$ which are $R$-linear (`hΔgal`); the existence, for each generator $g$, of a compatible system of coalgebra endomorphisms of the levels inducing the Hecke operator `genOpH M H S g` through $\Delta$ (`hΔhecke`); the levelwise description `he` of $e$ through $\Delta$, its injectivity (`heinj`), the description `herange` of its image as those Tate vectors all of whose components lie in `O.finPts (p ^ n)`, the saturation property `hsat` that $p\,y$ in the image forces $y$ in the image, and `hcoker`, that the quotient $T_pJ/\mathrm{im}(e)$ is $\mathbb{Z}_p$-linearly isomorphic to $\mathbb{Z}_p^{O.\mathrm{toricRank}}$; and `htor`, that every element of `O.toricPts (p ^ v)` comes from a level-$v$ point of $\mathcal{G}$.
--
--   The toric quotient data consist of a $p$-divisible group $\mathcal{B}$ over $R$ of height $h_B$ with a levelwise system of coalgebra maps $\psi_v : \mathcal{B}.\mathrm{level}\,v \to \mathcal{G}.\mathrm{level}\,v$, a natural number $h'$, and: $h = O.\mathrm{toricRank} + h_B$ (`hhB`), $h_B = 2h'$ (`hhB2`), compatibility of $\psi$ with the transition maps (`hψt`), the characterisation `hψker` that the image of a level-$v$ point of $\mathcal{G}$ under $\psi_v$ is trivial exactly when its image under $\Delta$ lies in `O.toricPts (p ^ v)`, surjectivity of $\psi_v$ on points (`hψsurj`), the statement `hψred` that a point of $\mathcal{G}$ whose image in $\mathcal{B}$ reduces to the identity at $\mathfrak{P}$ itself reduces to the identity, and `hperiod`, that for $\sigma$ in the inertia subgroup, $z$ in the $p^v$-torsion of $\mathrm{Pic}^0$ and a level-$v$ point $y$ with $\Delta(y) = \sigma\cdot z - z$, the image of $y$ in $\mathcal{B}$ reduces to the identity at $\mathfrak{P}$.
--
--   The scheme-level realisation consists of a ring homomorphism $\rho_h : R_p \to R$ and morphisms $\iota_v : \operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v) \to O.G$, subject to `hρh` (compatibility of $\rho_h$ with the embeddings into $\bar{\mathbb{Q}}$), `hιbase` ($\iota_v$ lies over $\operatorname{Spec}$ of $\rho_h$), `hιcl` (the induced morphism to the fibre product is a closed immersion), `hιp` ($\iota_v$ is killed by multiplication by $p^v$ in $O.L$), `hιpts` ($\iota_v$ computes $O.\mathrm{pts} \circ \Delta$ on points), `hιmul` ($\iota_v$ is a homomorphism for $O.L$ on points over any $R$-algebra), `hιt` (compatibility with the transitions), `hιhecke` (for each generator $g$, a compatible system of coalgebra endomorphisms of the levels intertwining $\iota$ with the Hecke correspondence `O.hecke S g` and inducing `genOpH M H S g` through $\Delta$), and `hιfin`, that the comparison morphism from $\operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v)$ to the $p^v$-torsion of $O.G$ pulled back to $R$ is an open and closed immersion whose image contains every point above the closed point of $R$.
--
--   The Atkin–Lehner data are: a semilinear automorphism `wgen` of `xHFunctionFieldBar M H` over $\bar{\mathbb{Q}}$, satisfying `hwgen`, namely that for geometric points $y, y'$ of the curve model related through the involution `𝔛.w`, the associated places satisfy $\mathrm{place}(y') = \mathrm{wgen}\cdot \mathrm{place}(y)$; a $\bar{\mathbb{Q}}$-algebra automorphism $\theta$ of `xHFunctionFieldBar M H` which by `hθ` sends a function coming from level $M/p$ to the $p$-fold $q$-expansion rescaling `qExpand` of its Laurent series; and `hwθ`, that `wgen` is the semilinear automorphism attached to $\theta$.
--
--   The degeneracy data, stated in the presence of `NeZero (M / p)` and of the existence of principal divisors for both function fields, are: additivity of $\Lambda.\mathrm{pts}$ (`hΛpts_add`) and of $\Lambda.\mathrm{ptsSp}$ for the base-changed group law on the special fibre (`hΛptsSp_add`); two $\bar{\mathbb{Q}}$-algebra maps $\alpha_H, \beta_H$ from the level-$(M/p)$ function field to the level-$M$ one, each integral, finite, and satisfying the fundamental identity and the pushforward norm formula (`hαHint`, `hαHFI`, `hαHfin`, `hαHN`, `hβHint`, `hβHFI`, `hβHfin`, `hβHN`); the statements `hdeg0` and `hdeg1` that `O.degPts 0` and `O.degPts 1` are computed on divisor classes by pushforward along $\alpha_H$ and along $\beta_H$ respectively; additive endomorphisms $F, F^{-1}, F^*$ of $\mathrm{Pic}^0$ of the special fibre `Fbar p M H hpM (ResidueField ↥Pl)` with $F$ the $q$-expansion Frobenius pushforward `qExpFrobeniusPushforwardModL` (`hF`), $F$ and $F^{-1}$ mutually inverse (`hFinv`), and $F^* = p\,F^{-1}$ (`hFstar`); a unit `pb` of $\mathbb{Z}/(M/p)$ reducing to $p$ (`hpb`) and the endomorphism $\delta$ given by the diamond action of its $\Gamma_0$-lift on the special fibre (`hδ`); two additive maps $\alpha\mathrm{pull}_i : \mathrm{JH}(M/p) \to J$ and two morphisms $\mathrm{degPull}_i$ over the base from $\Lambda.X$ to $O.G$ ($i \in \{0,1\}$) with `hpull` (the maps are induced by the morphisms on points), `hpull_mul` (the morphisms are homomorphisms for the group laws), `hpullsp` (on the special fibre, composition with $\mathrm{degPull}_i$ corresponds under the glued $\mathrm{Pic}^0$ description to $z \mapsto (z, F^*z)$ for $i = 0$ and $z \mapsto (F^*z, \delta z)$ for $i = 1$), and `hpullα`, `hpullβ` (on divisor classes, $\alpha\mathrm{pull}_0$ and $\alpha\mathrm{pull}_1$ are pullback along $\alpha_H$ and along $\beta_H$).
--
--   Under these hypotheses the conclusion asserts the existence of a $\mathbb{Z}_p$-linear endomorphism $e'$ of $T_pJ$ and of a function $B : J \times J \to \bar{\mathbb{Q}}$ with the following properties. Write $C$ for the image under [`TateModule.proj p J 1`](def/EllipticCurve_TateModule.html#L122) of the corner submodule $e_{i_0}\cdot T_pJ$ (the range of multiplication by $S'.e\,i_0$), and $C'$ for the image under the same map of the range of $e'$; both are subgroups of $J$.
--
--   First, $e' \circ e' = e'$. Secondly, $e'$ commutes with `JH.tateGaloisRep M H p τ` for every automorphism $\tau$ of $\bar{\mathbb{Q}}$ over $\mathbb{Q}$.
--
--   Thirdly, $B(x,y)^p = 1$ for all $x \in C$ and $y \in C'$. Fourthly, $B(x + x', y) = B(x,y)\,B(x',y)$ for $x, x' \in C$ and $y \in C'$; and fifthly, $B(x, y + y') = B(x,y)\,B(x,y')$ for $x \in C$ and $y, y' \in C'$.
--
--   Sixthly, the pairing is nondegenerate on the left: if $x \in C$ and $B(x,y) = 1$ for every $y \in C'$, then $x = 0$; and seventhly, on the right: if $y \in C'$ and $B(x,y) = 1$ for every $x \in C$, then $y = 0$.
--
--   Eighthly, for every $\sigma$ in `Pl.inertiaSubgroupIn ℚ` and all $x \in C$, $y \in C'$ one has $B(\sigma\cdot x, \sigma\cdot y) = \sigma(B(x,y))$.
--
--   Ninthly, for $a \in C \cap$ `O.finPts p`, the condition that $B(a,y) = 1$ for every $y \in C' \cap$ `O.finPts p` holds if and only if $a \in C \cap$ `O.toricPts p`; and tenthly, for $y \in C' \cap$ `O.finPts p`, the condition that $B(a,y) = 1$ for every $a \in C \cap$ `O.finPts p` holds if and only if $y \in C' \cap$ `O.toricPts p`.
--
--   Eleventhly, the sets $C' \cap$ `O.toricPts p` and $C \cap$ `O.toricPts p` have equal `Set.ncard`. Twelfthly, the same equality of cardinalities holds for the inertia-cyclotomic parts: the set of $y \in C'$ such that for every $\sigma \in$ `Pl.inertiaSubgroupIn ℚ` and every natural number $c$ with $\sigma\zeta = \zeta^c$ for all $\zeta \in \bar{\mathbb{Q}}$ with $\zeta^p = 1$ one has $\sigma\cdot y = c\,y$, and the corresponding set of such $x \in C$, have equal `Set.ncard`.
--
--   This is the duality input for the local analysis at $p$ of the $p$-torsion of the Jacobian of $X_H(M)$ with $p \parallel M$: it produces an idempotent cutting out a corner dual to the $U_p$-ordinary corner together with a $\mu_p$-valued, inertia-equivariant pairing between the two corners whose radicals on the finite-part points are exactly the toric points, and it records that the toric and the inertia-cyclotomic parts of the two corners have the same cardinality. It is used by [`ModularCurve.JHNeronObjectAtP.ncard_corner_finPts_mul_toricPts_eq_ncard_reducesToOne_mul_cyclotomic_of_abelJacobiPin_of_levelData_of_algEquiv`](thm.html#ModularCurve.JHNeronObjectAtP.ncard_corner_finPts_mul_toricPts_eq_ncard_reducesToOne_mul_cyclotomic_of_abelJacobiPin_of_levelData_of_algEquiv), where these counts enter the Cartier-duality computation underlying level lowering at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_idempotent_pairing_corner_adjointCorner_perfect_galois_radical_ncard_toric_cyclotomic_eq_of_abelJacobiPin_of_levelData_of_algEquiv.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_ModularCurve_XHDiamondModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

set_option maxHeartbeats 400000 in
open ModularCurve in

theorem ModularCurve.JHNeronObjectAtP.exists_idempotent_pairing_corner_adjointCorner_perfect_galois_radical_ncard_toric_cyclotomic_eq_of_abelJacobiPin_of_levelData_of_algEquiv
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (hfaith : ∀ t : 𝕋, (∀ x : TateModule p (ModularCurve.JH M H), t • x = 0) → t = 0)
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (hord : op (CohCarrier.Gen.U p Fact.out hpM) ∉ S'.𝔪 i₀)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (ModularCurve.JZeroNeronObjectAtP.baseRing p) Λ.f)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    (R : Type) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    [Algebra R (AlgebraicClosure ℚ)] [FaithfulSMul R (AlgebraicClosure ℚ)]
    (hRA : ∀ x : R, algebraMap R (AlgebraicClosure ℚ) x ∈ Pl)
    (hRdvr : IsDiscreteValuationRing R) (hRirr : Irreducible ((p : ℕ) : R))
    (hRfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ Pl.inertiaSubgroupIn ℚ ↔ ∀ x : R, σ (algebraMap R (AlgebraicClosure ℚ) x) = algebraMap R (AlgebraicClosure ℚ) x)
    (hRmax : ∀ y ∈ Pl, (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : R, algebraMap R (AlgebraicClosure ℚ) x = y)

    {h : ℕ}
    (𝒢 : PDivisibleGroup R p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H))
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[R] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[R] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
    (he : ∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
      ((e x : TateModule p (ModularCurve.JH M H)) : ℕ → ModularCurve.JH M H) n =
        Δ ((x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n))
    (heinj : Function.Injective e)
    (herange : ∀ y : TateModule p (ModularCurve.JH M H), y ∈ LinearMap.range e ↔
      ∀ n : ℕ, (y : ℕ → ModularCurve.JH M H) n ∈ O.finPts (p ^ n))
    (hegal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ x : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
        e (𝒢.tateModuleRep (AlgebraicClosure ℚ) τ' x) = ModularCurve.JH.tateGaloisRep M H p τ (e x))
    (hsat : ∀ y : TateModule p (ModularCurve.JH M H), (p : ℤ_[p]) • y ∈ LinearMap.range e → y ∈ LinearMap.range e)
    (hcoker : Nonempty ((TateModule p (ModularCurve.JH M H) ⧸ LinearMap.range e) ≃ₗ[ℤ_[p]] (Fin O.toricRank → ℤ_[p])))
    (htor : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    {hB : ℕ}
    (ℬ : PDivisibleGroup R p hB)
    (ψ : ∀ v : ℕ, ℬ.level v →ₐc[R] 𝒢.level v)
    {h' : ℕ}
    (hhB : h = O.toricRank + hB)
    (hhB2 : hB = 2 * h')
    (hψt : ∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (ℬ.transition v))
    (hψker : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[R] 𝒢.level v)) =
          (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v))
    (hψsurj : ∀ (v : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[R] 𝒢.level v)) = b)
    (hψred : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[R] 𝒢.level v))) a -
          algebraMap R (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : 𝒢.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom x a -
          algebraMap R (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (hperiod : ∀ (v : ℕ), ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ z ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) (p ^ v),
      ∀ y : 𝒢.Point (AlgebraicClosure ℚ) v,
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = σ • z - z →
        (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (ψ v : ℬ.level v →ₐ[R] 𝒢.level v))) a -
          algebraMap R (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (ρh : ModularCurve.XHDRLevel.R p →+* R)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hρh : (algebraMap R (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap R (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap R (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap R (𝒢.level v)))) h1))
    (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιpts : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[R] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)
    (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[R] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[R] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[R] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)
    (hιhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[R] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S g).1) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[R] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
    (hιfin : ∀ (v : ℕ)
      (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap R (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap R (𝒢.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρh))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint R →
          x ∈ Set.range jv.base)

    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwθ : wgen = SemilinearAut.ofAlgAut θ)

    [NeZero (M / p)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαHint : αH.toRingHom.IsIntegral)
    (hαHFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) αH hαHint)
    (hαHfin : FiniteAlong (AlgebraicClosure ℚ) αH)
    (hαHN : NormFormulaAlong (AlgebraicClosure ℚ) αH hαHfin)
    (hβHint : βH.toRingHom.IsIntegral)
    (hβHFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) βH hβHint)
    (hβHfin : FiniteAlong (AlgebraicClosure ℚ) βH)
    (hβHN : NormFormulaAlong (AlgebraicClosure ℚ) βH hβHfin)
    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαHint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hdeg1 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong βH hβHint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 1 (Pic0.mk Dv) = Pic0.mk Dw)
    (F Finv Fstar : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥Pl) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)
    (pb : (ZMod (M / p))ˣ)
    (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)
    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))
    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt Pl ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))
    (hpullα : ∀ Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
      αpull 0 (Pic0.mk Dw) = Pic0.mk ⟨Divisor.pullbackAlong αH hαHint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        Divisor.pullbackAlong_mem_degZero αH hαHint hαHFI Dw.2⟩)
    (hpullβ : ∀ Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
      αpull 1 (Pic0.mk Dw) = Pic0.mk ⟨Divisor.pullbackAlong βH hβHint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        Divisor.pullbackAlong_mem_degZero βH hβHint hβHFI Dw.2⟩)
    :
    ∃ (e' : Module.End ℤ_[p] (TateModule p (ModularCurve.JH M H))) (B : ModularCurve.JH M H → ModularCurve.JH M H → AlgebraicClosure ℚ),

      e' ∘ₗ e' = e' ∧
      (∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        e' ∘ₗ ModularCurve.JH.tateGaloisRep M H p τ = ModularCurve.JH.tateGaloisRep M H p τ ∘ₗ e') ∧

      (∀ x y : ModularCurve.JH M H, x ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) → y ∈ ((LinearMap.range e').toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) → B x y ^ p = 1) ∧
      (∀ x x' y : ModularCurve.JH M H, x ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) → x' ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) → y ∈ ((LinearMap.range e').toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) →
        B (x + x') y = B x y * B x' y) ∧
      (∀ x y y' : ModularCurve.JH M H, x ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) → y ∈ ((LinearMap.range e').toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) → y' ∈ ((LinearMap.range e').toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) →
        B x (y + y') = B x y * B x y') ∧

      (∀ x : ModularCurve.JH M H, x ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) → (∀ y : ModularCurve.JH M H, y ∈ ((LinearMap.range e').toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) → B x y = 1) → x = 0) ∧
      (∀ y : ModularCurve.JH M H, y ∈ ((LinearMap.range e').toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) → (∀ x : ModularCurve.JH M H, x ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) → B x y = 1) → y = 0) ∧

      (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ x y : ModularCurve.JH M H, x ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) → y ∈ ((LinearMap.range e').toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) → B (σ • x) (σ • y) = σ (B x y)) ∧

      (∀ a : ModularCurve.JH M H, (a ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) ∧ a ∈ O.finPts p) →
        ((∀ y : ModularCurve.JH M H, (y ∈ ((LinearMap.range e').toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) ∧ y ∈ O.finPts p) → B a y = 1) ↔ (a ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) ∧ a ∈ O.toricPts p))) ∧
      (∀ y : ModularCurve.JH M H, (y ∈ ((LinearMap.range e').toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) ∧ y ∈ O.finPts p) →
        ((∀ a : ModularCurve.JH M H, (a ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) ∧ a ∈ O.finPts p) → B a y = 1) ↔ (y ∈ ((LinearMap.range e').toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) ∧ y ∈ O.toricPts p))) ∧

      (Set.ncard {y : ModularCurve.JH M H | y ∈ ((LinearMap.range e').toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) ∧ y ∈ O.toricPts p} =
        Set.ncard {x : ModularCurve.JH M H | x ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) ∧ x ∈ O.toricPts p}) ∧
      (Set.ncard {y : ModularCurve.JH M H | y ∈ ((LinearMap.range e').toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) ∧
          (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ,
            (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • y = c • y)} =
        Set.ncard {x : ModularCurve.JH M H | x ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) ∧
          (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ,
            (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • x = c • x)}) := by sorry
