-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_isInvertible_presentation_frames_slopeLaw_fixed_base_strict_of_dvd_width
-- name    : ModularCurve.XHDRModelAtP.exists_isInvertible_presentation_frames_slopeLaw_fixed_base_strict_of_dvd_width
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/41c925cc-6600-5921-ab0b-8642cad44fb8
-- title:
--   Invertible module framing nodes, fixed places and a base point
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and $H \le (\mathbb Z/M)^\times$ is a subgroup containing the kernel of the reduction $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$, in the form `hHp`: every unit sent to $1$ by `ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)` lies in $H$. The hypothesis `hj` states that the $q$-series `jqModC ℚ` lies in the level-one $q$-expansion field `qExpFunctionFieldC ℚ ⊤`, and $\mathfrak X$ is a term of `XHDRModelAtP p M H hpM hj`: a Deligne–Rapoport-type datum at $p$ for the two-chart integral model `X p (ΓM M H) hj` over $R_p$, carrying among its fields a curve model $\mathfrak X.\mathrm{Meta}$ over $\overline{\mathbb Q}$ with function field $F_M :=$ `xHFunctionFieldBar M H`, an isomorphism $\mathfrak X.\mathrm{eeta}$ of $\mathfrak X.\mathrm{Meta}.C$ with the geometric generic fibre, an automorphism $\mathfrak X.w$, and, for a valuation subring as below, the special-fibre data $\mathfrak X.\mathrm{Mfib}$ (a curve model over the residue field), the two component maps $\mathfrak X.\mathrm{comp}\,i$ ($i \in \{0,1\}$) into the fibre and the map $\mathfrak X.\mathrm{efib}$; here, as in `CurveModel`, a curve model over a field consists of a smooth proper integral curve, an isomorphism of the given field of functions with its function field, and a bijection `placeOfPoint` from its closed points onto the places of that field, compatible with the stalks.
--
--   The coefficient data: $A$ is a valuation subring of $\overline{\mathbb Q}$ with `A.LiesOverPrime p`, i.e. $p$ is a non-unit of $A$, whose residue field $\kappa :=$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed, and $\rho : R_p \to A$ is a ring homomorphism with `hρ`: composing $\rho$ with the inclusion $A \hookrightarrow \overline{\mathbb Q}$ gives the structure map $R_p \to \overline{\mathbb Q}$. Write $\bar F :=$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field `qExpFunctionFieldC κ (ΓN p M H hpM)` over $\kappa$, and $\Phi :=$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`, the pullback of a place of $\bar F$ along the $p$-power Frobenius of that field.
--
--   The diamond datum: $pb$ is a unit of $\mathbb Z/(M/p)$ whose underlying element is $p$ (`hpb`), and $\delta$ is a self-map of the places of $\bar F$ which by `hδ` is the translation action of the semilinear automorphism `SemilinearAut.ofAlgAut` attached to `diamondActionModL κ (M / p) (infSubgroup p M H hpM)` evaluated at the chosen lift [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$ to $\Gamma_0(M/p)$, where `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb Z/(M/p))^\times$. The finset $SS$ of pairs of places of $\bar F$ is, by `hSS`, exactly `ssNodePairsQExp κ (ΓN p M H hpM) p`, the set of pairs $(\Phi(v),v)$ with $v$ in `ssPlacesQExp κ (ΓN p M H hpM) p`.
--
--   The specialisation datum: $\theta$ is a $\overline{\mathbb Q}$-algebra automorphism of $F_M$, and $\alpha$ is a $\overline{\mathbb Q}$-algebra map from $F_{M/p} :=$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` to $F_M$, with $\alpha$ integral (`hα`) and $\beta := \theta \circ \alpha$ integral (`hβ`); `hα_coe` says that $\alpha$ is the identity on underlying Laurent series. `Psp` is a `JHPlaceSpecialization p M H hpM A`, comprising a surjective specialisation map $\mathrm{sp}$ from the places of $F_{M/p}$ to the places of $\bar F$ together with its divisor-theoretic and inertia/Frobenius compatibilities, and `Rpd` is a `JHPlaceSpecialization.ProlongationDatum Psp θ`, comprising two regular prolongations $R_1, R_2$ (each with a set `integers` of elements of $F_M$ and a residue map to $\bar F$) linked by $\theta$. For a place $W$ of $F_M$ one writes $\mathrm{red}_1 W := \mathrm{sp}(W|_\alpha)$ (`Psp.reduceFst`) and $\mathrm{red}_2 W := \delta(\mathrm{sp}(W|_\beta))$ (`Psp.reduceSnd`); a place $v$ of $\bar F$ is `Fixed` when $\Phi(\delta(\Phi(v))) = v$; $W$ is `IsStrictFst` when $\delta(\Phi(\mathrm{red}_1W)) = \mathrm{red}_2W$ and $\mathrm{red}_1W$ is not `Fixed`, and `IsStrictSnd` when $\mathrm{red}_1W = \Phi(\mathrm{red}_2W)$ and $\mathrm{red}_2W$ is not `Fixed`. The hypothesis `hwgen` says that $\theta$ computes the effect of $\mathfrak X.w$ on places: if two $\overline{\mathbb Q}$-points $y,y'$ of $\mathfrak X.\mathrm{Meta}.C$ over the base satisfy $y' \ggg \mathrm{eeta} \ggg \mathrm{pr}_1 \ggg \mathfrak X.w = y \ggg \mathrm{eeta} \ggg \mathrm{pr}_1$, then `pointEquivPlace y'` is the translate of `pointEquivPlace y` by the semilinear automorphism of $\theta$. The hypothesis `hTD` is `Psp.TypeDichotomy`: every place $W$ of $F_M$ satisfies $\mathrm{red}_1W = \Phi(\mathrm{red}_2W)$ or $\delta(\Phi(\mathrm{red}_1W)) = \mathrm{red}_2W$; and `hmodel` is `Rpd.IsModel α β hα hβ δ`, the conjunction of the two divisor laws and the two cusp laws for $R_1,R_2$.
--
--   The two compatibility hypotheses `hcompat` and `hcompat'` both run over $i \in \{0,1\}$, a $\overline{\mathbb Q}$-point $y$ of $\mathfrak X.\mathrm{Meta}.C$ over the base, a lift $u$ of $\operatorname{Spec}\rho$ to the model, a $\kappa$-point $u_\kappa$ of the fibre `fibre ((residue A).comp ρ)`, the three displayed compatibilities between $y$, $u$, $u_\kappa$ and the reduction maps, and a closed point $P_0$ of $(\mathfrak X.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ whose image under $\mathrm{efib} \ggg \mathrm{comp}\,i$ is the closed point of $u_\kappa$. Under these, `hcompat` asserts that the place of $P_0$ equals $\mathrm{red}_1(\text{place of }y)$ if $i = 0$ and $\mathrm{red}_2(\text{place of }y)$ if $i = 1$, while `hcompat'` asserts that for $i = 0$ one has $\mathrm{red}_2(\text{place of }y) = \delta(\Phi(\text{place of }P_0))$ and for $i = 1$ one has $\mathrm{red}_1(\text{place of }y) = \Phi(\text{place of }P_0)$.
--
--   The annulus datum: $e : SS \to \mathbb N$ with $e(s) > 0$ for all $s$ (`he`), and for each $s \in SS$ an [`AlgebraicCurve.Annulus A F_M`](def/AlgebraicCurve_SemistableCharts.html#L86), i.e. a set $\mathrm{dom}(An_s)$ of places of $F_M$, a parameter $\mathrm{param}_s \in F_M$ and a modulus in the maximal ideal of $A$ subject to the axioms of `Annulus`. The hypothesis `hAn` imposes for each $s$ seven clauses: (1) $\mathrm{dom}(An_s)$ consists exactly of the places $W$ with $\mathrm{red}_1W = s_1$ which are neither `IsStrictFst` nor `IsStrictSnd`; (2) the modulus is $p^{e(s)}$ times a unit of $A$; (3) $\mathrm{param}_s$ is fixed by `arithmeticGalois (xHFunctionField M H) σ` for every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`; (4) the image in $F_M$ of the inverse of the modulus, times $\mathrm{param}_s$, lies in the integers of $R_1$; (5) $\mathrm{param}_s$ lies in the integers of $R_2$ with non-zero $R_2$-residue; (6) for $\mathrm{param}_s$ in the integers of $R_2$ one has $\mathrm{ord}_{s_2}$ of its $R_2$-residue equal to $1$, and for every $f$ in the integers of $R_2$ with non-zero $R_2$-residue and $\mathrm{ord}_P f = 0$ at all $P \in \mathrm{dom}(An_s)$, the value $P(f)\,P(\mathrm{param}_s)^{-\mathrm{ord}_{s_2}(\bar f)}$ lies in $A$ and is a unit there, for every $P \in \mathrm{dom}(An_s)$; (7) the same with $R_1$ and the element $(\text{modulus})\cdot\mathrm{param}_s^{-1}$ in place of $R_2$ and $\mathrm{param}_s$, and $s_1$ in place of $s_2$. Finally $k$ is a natural number divisible by every $e(s)$ (`hk`).
--
--   The geometric datum: $\mathfrak X_A :=$ `pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))`, assumed integral; $gA : \mathfrak X.\mathrm{Meta}.C \to \mathfrak X_A$ satisfies `hgA₁` ($gA$ followed by the first projection is $\mathrm{eeta}$ followed by the first projection) and `hgA₂` ($gA$ followed by the second projection is $\mathfrak X.\mathrm{Meta}.\mathrm{toBase}$ followed by `barPt A`); $bc$ maps the fibre `fibre ((residue A).comp ρ)` to $\mathfrak X_A$ with `hbc₁`, `hbc₂` the two displayed compatibilities with the projections. Moreover $eK$ is a ring isomorphism of the function field of $\mathfrak X_A$ with $F_M$, and `heK` says that for every open $U$ (with the two non-emptiness assumptions) and every section $a$ over $U$, $eK$ of the germ of $a$ in the function field is the $F_M$-element $\mathfrak X.\mathrm{Meta}.\mathrm{ffEquiv}^{-1}$ of the germ of $(gA)^\ast a$ over $gA^{-1}U$.
--
--   The local-principality hypothesis `hloc`: for every $s \in SS$ and every point $n$ of `pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)` with $\mathfrak X.\mathrm{placeOn0}\,n = s_1$ and $\mathfrak X.\mathrm{placeOn1}\,n = s_2$ (so $n$ is the crossing attached, through `nodeEquiv`, to the supersingular place $s_2$ and its Frobenius pullback $s_1$), there are an open $U \subseteq \mathfrak X_A$ containing the image of $n$ under $bc$ and the first projection followed by $\mathrm{comp}\,0$, with $gA^{-1}U$ non-empty, and a section $t$ over $U$, whose associated function $g_t \in F_M$ (the $\mathrm{ffEquiv}^{-1}$ of the germ of $(gA)^\ast t$) satisfies: there is $a \ne 0$ in $\overline{\mathbb Q}$ with $\mathrm{ord}_P g_t = 0$ and $P(g_t)\,a\,P(\mathrm{param}_s)^{-(k/e(s))}$ a unit of $A$ for all $P \in \mathrm{dom}(An_s)$; the germ of $t$ is a unit at the image of every closed point $Q$ of $\mathfrak X.\mathrm{Mfib}.C$ under $\mathrm{efib} \ggg \mathrm{comp}\,1$ lying in $U$ and distinct from the image of $n$; at the image of every closed point $Q$ under $\mathrm{efib} \ggg \mathrm{comp}\,0$ lying in $U$ and distinct from the image of $n$ there are a smaller open $W \le U$ and a section $t_0$ on $W$ with $t|_W = p^k t_0$ and $t_0$ of unit germ; and $\mathrm{ord}$ of $g_t$ at the place of $x$ vanishes for every closed point $x$ of $\mathfrak X.\mathrm{Meta}.C$ with $gA(x) \in U$.
--
--   Conclusion. There exist a module $\mathcal L$ on $\mathfrak X_A$, a proof that $\mathcal L$ is invertible in the sense of `Scheme.Modules.IsInvertible` (each point has a neighbourhood on which the pullback of $\mathcal L$ is isomorphic to the unit module), and additive maps $\varphi_U : \Gamma(\mathcal L, U) \to K(\mathfrak X_A)$ for all opens $U$, such that:
--
--   (i) for $V \le U$ with $V$ non-empty and $m \in \Gamma(\mathcal L, U)$, $\varphi_V(m|_V) = \varphi_U(m)$;
--
--   (ii) for non-empty $U$, $a \in \Gamma(\mathfrak X_A, U)$ and $m \in \Gamma(\mathcal L, U)$, $\varphi_U(a \cdot m)$ is the image of $a$ in $K(\mathfrak X_A)$ times $\varphi_U(m)$;
--
--   (iii) $\varphi_U$ is injective for every non-empty $U$;
--
--   (iv) (frames at the crossings) for every $s \in SS$ and every crossing $n$ with $\mathfrak X.\mathrm{placeOn0}\,n = s_1$, $\mathfrak X.\mathrm{placeOn1}\,n = s_2$, there are a non-empty open $U$ containing the image of $n$ under $bc$ and the first projection followed by $\mathrm{comp}\,0$, a section $m \in \Gamma(\mathcal L, U)$ and $g = eK(\varphi_U m) \in F_M$ such that $m$ is a frame on $U$ (`Scheme.Modules.IsFrameOn`: multiplication by the restriction of $m$ is bijective from sections of the structure sheaf to sections of $\mathcal L$ on every smaller open), $g \ne 0$, and there is $a \ne 0$ in $\overline{\mathbb Q}$ with $\mathrm{ord}_P g = 0$ and $P(g)\,a\,P(\mathrm{param}_s)^{-(k/e(s))}$ a unit of $A$ for every $P \in \mathrm{dom}(An_s)$;
--
--   (v) (frames at the fixed places of the first component) for every closed point $Q$ of $\mathfrak X.\mathrm{Mfib}.C$ whose place $v_Q$ is `Fixed` for $\delta$ and differs from the first component of every pair in $SS$, there are a non-empty open $U$ containing $bc$ of the image of $Q$ under $\mathrm{efib} \ggg \mathrm{comp}\,0$, a section $m \in \Gamma(\mathcal L,U)$ and $g = eK(\varphi_U m)$ such that $m$ is a frame on $U$, $\mathrm{ord}_V g = 0$ for every place $V$ of $F_M$ with $\mathrm{red}_1 V = v_Q$, and there is $c \in \overline{\mathbb Q}$ with $c \cdot g$ in the integers of $R_1$, its $R_1$-residue non-zero, and $\mathrm{ord}_{v_Q}$ of that residue equal to $0$;
--
--   (vi) (frames at the fixed places of the second component) for every closed point $Q$ such that $\Phi(v_Q)$ is `Fixed` for $\delta$ and differs from the first component of every pair in $SS$, there are a non-empty open $U$ containing $bc$ of the image of $Q$ under $\mathrm{efib} \ggg \mathrm{comp}\,1$, a section $m \in \Gamma(\mathcal L,U)$ and $g = eK(\varphi_U m)$ such that $m$ is a frame on $U$ and $\mathrm{ord}_V g = 0$ for every place $V$ of $F_M$ with $\mathrm{red}_1V = \Phi(v_Q)$ and $\mathrm{red}_2V = v_Q$;
--
--   (vii) (a single affine open, and a base point) there is an affine open $U_{\mathrm{aff}}$ of $\mathfrak X_A$ which contains the image of every crossing $n$ attached to a pair of $SS$ as in (iv), the image under $\mathrm{efib} \ggg \mathrm{comp}\,0$ of every closed point $Q$ as in (v), and the image under $\mathrm{efib} \ggg \mathrm{comp}\,1$ of every closed point $Q$ as in (vi); and furthermore there are a closed point $Q$ of $\mathfrak X.\mathrm{Mfib}.C$, a non-empty open $U$ containing the image of $Q$ under $\mathrm{efib} \ggg \mathrm{comp}\,0$ composed with $bc$, that image also lying in $U_{\mathrm{aff}}$, a section $m \in \Gamma(\mathcal L,U)$ and $g = eK(\varphi_U m)$ such that $v_Q$ differs from the first component of every pair in $SS$, $m$ is a frame on $U$, and some $c \in \overline{\mathbb Q}$ has $c\cdot g$ in the integers of $R_1$ with non-zero $R_1$-residue;
--
--   (viii) (strictness of the horizontal zeros) for every closed point $x$ of $\mathfrak X.\mathrm{Meta}.C$, every open $U$ with $gA(x) \in U$, every $m \in \Gamma(\mathcal L,U)$ which is a frame on $U$ and $g = eK(\varphi_U m)$: if the order of $g$ at the place of $x$ is non-zero, then that place is `IsStrictFst` or `IsStrictSnd` for $\alpha,\beta,\delta$.
--
--   This is the construction step producing the twisted invertible module on the Deligne–Rapoport model of $X_H(M)$ base-changed to a valuation ring $A$ over $p$ (with $p$ exactly dividing $M$), together with a presentation of its sections inside the function field and explicit local frames at the crossings of the special fibre, at the $\delta$-fixed non-nodal places of each of the two components, and at one base point inside a common affine open. It is used by [`ModularCurve.XHDRModelAtP.forall_annulus_exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_dvd_of_offDiag`](thm.html#ModularCurve.XHDRModelAtP.forall_annulus_exists_smul_mem_integers_isGoodDiv_ord_eq_zero_verticalSlope_of_dvd_of_offDiag), where the frames yield the slope law on the annuli governing the vertical components of divisors in the level-lowering argument at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_isInvertible_presentation_frames_slopeLaw_fixed_base_strict_of_dvd_width.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ModularCurve.XHDRModelAtP.exists_isInvertible_presentation_frames_slopeLaw_fixed_base_strict_of_dvd_width
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (k : ℕ) (hk : ∀ s : ↥SS, e s ∣ k)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))

    [IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]
    (eK : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H))
    (heK : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme U)] (a : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)),
      eK ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)))

    (hloc : ∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
      (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2),
      ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ U)
        (_ : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))) (t : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)),

        (∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) = 0 ∧
            ∃ h : P.evalAt (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ U),
          bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ≠ bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) → IsUnit (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ U _ hQ).hom t)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U),
          bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ≠ bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) →
          ∃ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hWU : W ≤ U) (hQW : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ W) (t₀ : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), W)),
            (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.map (homOfLE hWU).op t = ((p : ℕ) : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), W)) ^ k * t₀ ∧
            IsUnit (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ W _ hQW).hom t₀)) ∧

        (∀ (x : closedPoints 𝔛.Meta.C), gA.base x.1 ∈ U → (𝔛.Meta.placeOfPoint x).ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) = 0))
    :
    ∃ (𝓛 : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules) (_ : Scheme.Modules.IsInvertible 𝓛)
        (φ : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Γ(𝓛, U) →+ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField : Type)),

        (∀ (U V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(𝓛, U), φ V (𝓛.presheaf.map (homOfLE h).op m) = φ U m) ∧
        (∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty U] (a : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)) (m : Γ(𝓛, U)),
          φ U (a • m) = algebraMap Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a * φ U m) ∧
        (∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Nonempty U → Function.Injective (φ U)) ∧

        (∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
      (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2),
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧ g ≠ 0 ∧ (∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord (g) = 0 ∧
            ∃ h : P.evalAt (g) * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A))) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
          JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
          (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q → V.ord g = 0) ∧
            (∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0 ∧
              ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q).ord (Rpd.R₁.residue ⟨c • g, hc⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
          JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) →
          (∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1) →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
              Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q → V.ord g = 0)) ∧

        (∃ Uaff : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, IsAffineOpen Uaff ∧
          (∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2), bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ Uaff) ∧
          (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
            JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
          (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) → bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ Uaff) ∧
          (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
            JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) →
          (∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1) → bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ Uaff) ∧
          (∃ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ Uaff)
            (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U)) (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
              (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) ∧ Scheme.Modules.IsFrameOn m U ∧
              ∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0)) ∧

        (∀ (x : closedPoints 𝔛.Meta.C) (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens), gA.base x.1 ∈ U → ∀ (m : Γ(𝓛, U)) (g : ↥(xHFunctionFieldBar M H)), g = eK (φ U m) →
          Scheme.Modules.IsFrameOn m U → (𝔛.Meta.placeOfPoint x).ord g ≠ 0 →
          Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (𝔛.Meta.placeOfPoint x) ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ (𝔛.Meta.placeOfPoint x)) := by sorry
