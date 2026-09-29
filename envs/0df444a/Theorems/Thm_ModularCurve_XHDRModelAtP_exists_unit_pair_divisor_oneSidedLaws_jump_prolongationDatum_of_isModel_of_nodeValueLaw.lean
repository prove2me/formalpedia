-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_unit_pair_divisor_oneSidedLaws_jump_prolongationDatum_of_isModel_of_nodeValueLaw
-- name    : ModularCurve.XHDRModelAtP.exists_unit_pair_divisor_oneSidedLaws_jump_prolongationDatum_of_isModel_of_nodeValueLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/fbbe4b3b-8554-5947-8e89-298b82c46639
-- title:
--   Unit pair and one-sided divisor laws at the X_H model
-- statement:
--   Throughout, $p$ is a prime and $M$ a non-zero natural number with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and $H \le (\mathbb Z/M)^\times$ is a subgroup containing the kernel of the reduction $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$: the hypothesis `hHp` says that every unit $u$ with `ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1` lies in $H$. The hypothesis `hj` records that the $j$-series `jqModC ℚ` belongs to the $q$-expansion function field `qExpFunctionFieldC ℚ ⊤` of the full modular group. Write $F_M$ for `xHFunctionFieldBar M H` and $F_{M/p}$ for `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, the base changes to $\overline{\mathbb Q}$ of the $q$-expansion function fields at level $\Gamma_H(M)$ and at level $M/p$ for the image subgroup `infSubgroup p M H hpM` $= H \cdot \ker$ in $(\mathbb Z/(M/p))^\times$, both realised inside Laurent series over $\overline{\mathbb Q}$.
--
--   The datum $\mathfrak X$ is a term of the structure `XHDRModelAtP p M H hpM hj`, whose fields (summarised here) comprise: properness, flatness, integrality and normality on affine opens of the two-chart integral model `X p (ΓM M H) hj` over `R p`; properness and relative smoothness of dimension $1$ of `toBase p (ΓN p M H hpM) hj`; a curve model `𝔛.Meta` of $F_M$ over $\overline{\mathbb Q}$ (a proper smooth relative curve with function field identified with $F_M$ and a bijection `placeOfPoint` from closed points to places), an isomorphism `𝔛.eeta` of `𝔛.Meta.C` with the base change of the model along `algebraMap (R p) (AlgebraicClosure ℚ)` compatible with the structure morphisms, Galois equivariance `hgal` of the induced bijection `𝔛.Meta.pointEquivPlace` between $\overline{\mathbb Q}$-sections and places, the pinning `Meta_pin` of this identification on the finite chart, smoothness and geometric integrality of the generic fibre, together with the further fields used below: the isomorphism `𝔛.w`, and, for a place datum as in the next paragraph, the curve model `𝔛.Mfib A hA ρ hρ` of the fibre with its morphisms `𝔛.efib A hA ρ hρ` and the two component morphisms `𝔛.comp A hA ρ hρ i`, $i \in \{0,1\}$.
--
--   Next, $A$ is a valuation subring of $\overline{\mathbb Q}$ with `A.LiesOverPrime p`, that is $p$ lies in `A.nonunits`, whose residue field $\kappa =$ `ResidueField ↥A` is algebraically closed of characteristic $p$, and $\rho :$ `R p` $\to A$ is a ring homomorphism with `A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)` (`hρ`). Write $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field `qExpFunctionFieldC κ (ΓN p M H hpM)`, and $\Phi =$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` for the Frobenius operation on places of $\bar F$ over $\kappa$, given by restriction along the mod-$p$ Frobenius of the function field.
--
--   The unit `pb` $\in (\mathbb Z/(M/p))^\times$ has underlying element the class of $p$ (`hpb`). The map $\delta$ sends places of $\bar F$ over $\kappa$ to places of $\bar F$ over $\kappa$ and, by `hδ`, is the action through `SemilinearAut.ofAlgAut` of the diamond automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)`, the value at a chosen $\Gamma_0(M/p)$-lift of `pb` of the mod-$p$ diamond representation, acting on places by the pointwise action of semilinear automorphisms.
--
--   The finite set $SS$ of pairs of places of $\bar F$ over $\kappa$ is characterised by `hSS` as consisting exactly of the members of `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is the pairs $s$ with $s_2$ in `ssPlacesQExp κ (ΓN p M H hpM) p` and $s_1 = \Phi(s_2)$.
--
--   Further, $\theta$ is an $\overline{\mathbb Q}$-algebra automorphism of $F_M$, and $\alpha : F_{M/p} \to F_M$ is an $\overline{\mathbb Q}$-algebra homomorphism which is integral (`hα`), with $\beta = \theta \circ \alpha$ also integral (`hβ`). `Psp` is a term of `JHPlaceSpecialization p M H hpM A`, consisting of a map `sp` from places of $F_{M/p}$ over $\overline{\mathbb Q}$ to places of $\bar F$ over $\kappa$, a homomorphism `spPic0` on degree-zero divisor classes, and the compatibility clauses `d0_qexp`, `d4` (surjectivity of `sp`), `d5`, `d6_inertia`, `d6_frobenius` and `spPic0_compat`. `Rpd` is a term of `JHPlaceSpecialization.ProlongationDatum Psp θ`, consisting of two regular prolongations `R₁`, `R₂` of $A$ to $F_M$ with residue field $\bar F$ (each a valuation subring `integers` of $F_M$ with a surjective residue homomorphism onto $\bar F$ whose kernel is the maximal ideal, inducing $A$ on $\overline{\mathbb Q}$), together with `residue₁_coeffMap`, the equivalence `mem_integers₂_iff` ($f \in$ `R₂.integers` if and only if $\theta f \in$ `R₁.integers`) and `residue₂_eq` (the `R₂`-residue of $f$ is the `R₁`-residue of $\theta f$). For a place $W$ of $F_M$ one has `Psp.reduceFst α hα W` $=$ `Psp.sp` of the restriction of $W$ along $\alpha$, and `Psp.reduceSnd β hβ δ W` $= \delta$ applied to `Psp.sp` of the restriction of $W$ along $\beta$.
--
--   The remaining hypotheses are as follows.
--
--   `hwgen`: for all $\overline{\mathbb Q}$-sections $y, y'$ of `𝔛.Meta.toBase`, if $y'$ followed by `𝔛.eeta`, then by the first projection and then by `𝔛.w.hom`, equals $y$ followed by `𝔛.eeta` and the first projection, then `𝔛.Meta.pointEquivPlace y'` is the image of `𝔛.Meta.pointEquivPlace y` under the action of `SemilinearAut.ofAlgAut θ`.
--
--   `hθ`: whenever $f \in F_M$ and $u \in F_{M/p}$ have the same Laurent series, the Laurent series of $\theta f$ is `qExpand (AlgebraicClosure ℚ) p` of that of $u$, i.e. the substitution $q \mapsto q^p$. `hα_coe`: $\alpha$ is the identity on Laurent series, $\alpha u$ and $u$ having the same expansion.
--
--   `hTD`: `Psp.TypeDichotomy α β hα hβ δ`, i.e. for every place $W$ of $F_M$ either `reduceFst` $W = \Phi($`reduceSnd` $W)$ or $\delta(\Phi($`reduceFst` $W)) =$ `reduceSnd` $W$.
--
--   `hmodel`: `Rpd.IsModel α β hα hβ δ`, the conjunction of the four clauses `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty` (for $\alpha$) and `CuspLawZero` (for $\beta$ and $\delta$).
--
--   `hNV`: `Rpd.NodeValueLaw α β hα hβ δ SS`, i.e. for every $f \in F_M$ lying in both `R₁.integers` and `R₂.integers` with both residues non-zero, and every $s \in SS$ such that no place $V$ with $\operatorname{ord}_V f \neq 0$ satisfies both `reduceFst` $V = s_1$ and `reduceSnd` $V = s_2$, there is a non-zero $c \in \kappa$ at which $s_1$ takes the value $c$ on the `R₁`-residue of $f$ and $s_2$ takes the value $c$ on the `R₂`-residue of $f$.
--
--   `hcompat` and `hcompat'`: two compatibility clauses relating the places of closed points of the fibre model to the reductions of places of $F_M$. Both are quantified over $i \in \{0,1\}$, a $\overline{\mathbb Q}$-section $y$ of `𝔛.Meta.toBase`, a point $u$ of the model over `Spec.map (CommRingCat.ofHom ρ)` whose generic fibre is $y$ (`barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _`), a $\kappa$-point `uκ` of `fibre ((IsLocalRing.residue ↥A).comp ρ)` which is a section of the second projection and whose first projection is the reduction of $u$ along `IsLocalRing.residue ↥A`, and a closed point $P_0$ of `(𝔛.Mfib A hA ρ hρ).C` whose image under `𝔛.efib A hA ρ hρ` followed by `𝔛.comp A hA ρ hρ i` is the closed point determined by `uκ`. Under these hypotheses, `hcompat` asserts that `(𝔛.Mfib A hA ρ hρ).placeOfPoint P0` equals `Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)` if $i = 0$ and `Psp.reduceSnd β hβ δ (𝔛.Meta.pointEquivPlace y)` otherwise; `hcompat'` asserts that for $i = 0$ one has `Psp.reduceSnd β hβ δ (𝔛.Meta.pointEquivPlace y)` $= \delta(\Phi(\,$`placeOfPoint P0`$\,))$, and otherwise `Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)` $= \Phi(\,$`placeOfPoint P0`$\,)$.
--
--   Conclusion. There exist $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ on $F_M$ over $\overline{\mathbb Q}$ (finitely supported integer-valued functions on places) such that:
--
--   (1) $D_1(W) = \operatorname{ord}_W(u_1)$ and $D_2(W) = \operatorname{ord}_W(u_2)$ for every place $W$ of $F_M$ over $\overline{\mathbb Q}$.
--
--   (2) $u_1$ lies in `Rpd.R₁.integers`, and for this membership $h_1$: the residue `Rpd.R₁.residue ⟨u₁, h₁⟩` in $\bar F$ is non-zero; $u_1^{-1}$ also lies in `Rpd.R₁.integers`; for every place $v$ of $\bar F$ over $\kappa$ which is not `Fixed` for $\delta$, that is $\Phi(\delta(\Phi(v))) \neq v$, the value at $v$ of the pushforward along `Psp.reduceFst α hα` of `Psp.fstDiv α β hα hβ δ D₁` (the restriction of $D_1$ to the places satisfying `Psp.IsStrictFst α β hα hβ δ`) equals $\operatorname{ord}_v$ of that residue; and for every place $C$ of $F_M$ satisfying `JHPlaceSpecialization.IsInftySide`, the value at `Psp.reduceFst α hα C` of the pushforward along `Psp.reduceFst α hα` of the restriction of $D_1$ to the places satisfying `IsInftySide` equals the order at `Psp.reduceFst α hα C` of that residue. Here `IsInftySide W` means that $W$ is `IsCuspidal` and that there are $x, x' \in F_M$ with Laurent series `jqModC (AlgebraicClosure ℚ)` and `qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))` respectively, and a $\tau \in A$ with residue $1$ such that $W$ takes the value $\tau$ at $x'/x^p$.
--
--   (3) For every non-zero $f \in F_M$ there are $m \in \mathbb N$ with $m \neq 0$ and $j \in \mathbb Z$ such that $f^m u_1^{\,j}$ lies in `Rpd.R₂.integers` with non-zero `R₂`-residue.
--
--   (4) Symmetrically, $u_2$ lies in `Rpd.R₂.integers`, and for this membership $h_2$: the residue `Rpd.R₂.residue ⟨u₂, h₂⟩` is non-zero; $u_2^{-1}$ also lies in `Rpd.R₂.integers`; for every place $v$ of $\bar F$ which is not `Fixed` for $\delta$, the value at $v$ of the pushforward along `Psp.reduceSnd β hβ δ` of `Psp.sndDiv α β hα hβ δ D₂` (the restriction of $D_2$ to the places satisfying `Psp.IsStrictSnd α β hα hβ δ`) equals $\operatorname{ord}_v$ of that residue; and for every place $C$ of $F_M$ satisfying `JHPlaceSpecialization.IsZeroSide` — i.e. $C$ is `IsCuspidal'` and there are $x, x'$ with the two expansions above and a $\tau \in A$ with residue $1$ such that $C$ takes the value $\tau$ at $x/x'^p$ — the value at `Psp.reduceSnd β hβ δ C` of the pushforward along `Psp.reduceSnd β hβ δ` of the restriction of $D_2$ to the places satisfying `IsZeroSide` equals the order at `Psp.reduceSnd β hβ δ C` of that residue.
--
--   (5) For every non-zero $f \in F_M$ there are $m \in \mathbb N$ with $m \neq 0$ and $j \in \mathbb Z$ such that $f^m u_2^{\,j}$ lies in `Rpd.R₁.integers` with non-zero `R₁`-residue.
--
--   This is the modular-unit clause of the glueing input for $X_H(M)$ at a prime $p$ exactly dividing $M$: it asserts the existence, at the Deligne–Rapoport-type integral model, of two units of the respective Gauss prolongations $R_1$, $R_2$ whose divisors obey the one-sided divisor and cusp laws and which become non-units for the opposite prolongation after adjustment by a power of any given non-zero function. It is used by [`ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen), [`ModularCurve.XHDRModelAtP.exists_pic0Mk_eq_forall_isStrict_or_reduceFst_mem_of_prolongationDatum_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_pic0Mk_eq_forall_isStrict_or_reduceFst_mem_of_prolongationDatum_offDiag_of_wgen) and [`ModularCurve.XHDRModelAtP.ord_residue_eq_zero_of_fixed_of_forall_ord_eq_zero_fst_and_snd_of_offDiag`](thm.html#ModularCurve.XHDRModelAtP.ord_residue_eq_zero_of_fixed_of_forall_ord_eq_zero_fst_and_snd_of_offDiag), where it feeds the computation of the glued specialisation and of the component group of the reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_unit_pair_divisor_oneSidedLaws_jump_prolongationDatum_of_isModel_of_nodeValueLaw.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

open Classical in

theorem ModularCurve.XHDRModelAtP.exists_unit_pair_divisor_oneSidedLaws_jump_prolongationDatum_of_isModel_of_nodeValueLaw
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

    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0) := by sorry
