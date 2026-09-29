-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst
-- name    : ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/b5782812-7617-510e-b889-a1a35ac01745
-- title:
--   Residue-disc expansion of stalk germs at a strict place of the first kind
-- statement:
--   Fix a prime $p$ and a level $M$ with $p \mid M$ (`hpM`) but $p^2 \nmid M$ (`hpM2`), a subgroup $H \le (\mathbf Z/M)^\times$ containing every unit that becomes trivial under the reduction map $(\mathbf Z/M)^\times \to (\mathbf Z/(M/p))^\times$ (`hHp`), the hypothesis `hj` that the $q$-series `jqModC ℚ` lies in the $q$-expansion function field of the full modular group over $\mathbf Q$, and $\mathfrak X$, an `XHDRModelAtP p M H hpM hj`: a Deligne–Rapoport style integral model of $X_H$ over $R_p$ together with, among its data, a curve model `Meta` over $\overline{\mathbf Q}$ with function field $F :=$ `xHFunctionFieldBar M H`, an isomorphism `eeta` of `Meta.C` with the base change of `toBase p (ΓM M H) hj` along $R_p \to \overline{\mathbf Q}$, and the fibrewise data `Mfib`, `efib`, `comp`, `w` used below.
--
--   Arithmetic data: $A$ is a valuation subring of $\overline{\mathbf Q}$ lying over $p$ in the sense that $p$ is a non-unit of $A$ (`hA`), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, and $\rho : R_p \to A$ is a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbf Q}$ is the structure map $R_p \to \overline{\mathbf Q}$ (`hρ`). Write $\bar F :=$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field of $\Gamma_N(p,M,H)$ over $\kappa$.
--
--   Diamond operator: $pb$ is a unit of $\mathbf Z/(M/p)$ whose underlying residue class is $p$ (`hpb`), and $\delta$ is a self-map of the set of places of $\bar F$ over $\kappa$ which, by `hδ`, is the action on places of the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at a chosen lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$ to $\Gamma_0(M/p)$; here `infSubgroup p M H hpM` is the image of $H$ in $(\mathbf Z/(M/p))^\times$. The finite set $SS$ of pairs of places of $\bar F$ is required (`hSS`) to consist exactly of the pairs in `ssNodePairsQExp κ (ΓN p M H hpM) p`, i.e. those $(s_1,s_2)$ with $s_2$ in the set `ssPlacesQExp` of supersingular places and $s_1 =$ `qExpFrobeniusPlaceModL` $(s_2)$, the place obtained by restricting $s_2$ along the mod-$p$ Frobenius of the function field.
--
--   Degeneracy data: $\theta$ is an $\overline{\mathbf Q}$-algebra automorphism of $F$; $\alpha$ is an integral (`hα`) $\overline{\mathbf Q}$-algebra map from $F' :=$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` to $F$, with $\beta := \theta \circ \alpha$ also integral (`hβ`); `Psp` is a `JHPlaceSpecialization p M H hpM A`, i.e. a specialisation map $\mathrm{sp}$ from places of $F'$ over $\overline{\mathbf Q}$ to places of $\bar F$ over $\kappa$ together with a map on degree-zero divisor classes and the compatibility axioms of that structure; and `Rpd` is a `ProlongationDatum` for `Psp` and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F$ (valuation subrings `integers` with surjective residue homomorphisms onto $\bar F$ whose kernel is the maximal ideal) linked by $\theta$, and of the compatibility of $R_1$'s residue map with reduction of Laurent coefficients. Throughout, $\mathrm{red}_1(W) :=$ `Psp.reduceFst α hα W` $= \mathrm{sp}(W|_\alpha)$ and $\mathrm{red}_2(W) :=$ `Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W` $= \delta(\mathrm{sp}(W|_\beta))$, where $W|_\alpha$, $W|_\beta$ denote restriction of places along $\alpha$, $\beta$.
--
--   The remaining hypotheses are: `hwgen`, that for two $\overline{\mathbf Q}$-points $y, y'$ of `Meta.C` over the base, if $y'$ followed by `eeta`, the first pullback projection and $\mathfrak X.w$ agrees with $y$ followed by `eeta` and the first projection, then the place of $y'$ is the place of $y$ translated by $\theta$; `hα_coe`, that $\alpha$ is the identity on Laurent-series expansions, i.e. the Laurent series of $\alpha(u)$ is that of $u$; `hTD`, the type dichotomy for $(\alpha,\beta,\delta)$: every place $W$ of $F$ satisfies $\mathrm{red}_1(W) = \mathrm{Frob}_p(\mathrm{red}_2(W))$ or $\delta(\mathrm{Frob}_p(\mathrm{red}_1(W))) = \mathrm{red}_2(W)$; `hmodel`, that `Rpd` is a model for $(\alpha,\beta,\delta)$, i.e. the two divisor laws and the two cusp laws of `IsModel` hold; and two point-wise compatibility families, `hcompat` and `hcompat'`, each quantified over $i \in \{0,1\}$, a $\overline{\mathbf Q}$-point $y$ of `Meta.C`, an $A$-section $u$ of `toBase p (ΓM M H) hj` over $\mathrm{Spec}\,\rho$ whose composition with the $\overline{\mathbf Q}$-point of $\mathrm{Spec}\,A$ is the generic point determined by $y$, a $\kappa$-section $u_\kappa$ of the special fibre reducing $u$, and a closed point $P_0$ of the special-fibre curve model `Mfib` lying, via `efib` and the $i$-th component map `comp`, over the closed point of $u_\kappa$. Under those conditions, `hcompat` asserts that the place of $P_0$ equals $\mathrm{red}_1$ of the place of $y$ when $i = 0$ and $\mathrm{red}_2$ of the place of $y$ when $i = 1$, while `hcompat'` asserts the transposed relations: for $i = 0$, $\mathrm{red}_2$ of the place of $y$ equals $\delta$ applied to the Frobenius place of the place of $P_0$, and for $i = 1$, $\mathrm{red}_1$ of the place of $y$ equals the Frobenius place of the place of $P_0$.
--
--   The situation being analysed is this. $Q$ is a place of $F$ over $\overline{\mathbf Q}$ which is strict of the first kind (`hQ`): $\delta(\mathrm{Frob}_p(\mathrm{red}_1(Q))) = \mathrm{red}_2(Q)$ and the predicate `Fixed` fails for $\delta$ at $\mathrm{red}_1(Q)$. Further, $u$ is an $A$-section as above, $u_\kappa$ a $\kappa$-point of the fibre over $\kappa$, and $P_0$ a closed point of `Mfib`, subject to: `hu`, that $u$ restricted to $\overline{\mathbf Q}$ is the generic point attached to $Q$ under `Meta.pointEquivPlace`; `huκ₁` and `huκ₂`, that $u_\kappa$ is the reduction of $u$ and is a section of the fibre; `hP0`, that $P_0$ lies over the closed point of $u_\kappa$ through `efib` and the zeroth component; `hP0Q`, that the place of $P_0$ is $\mathrm{red}_1(Q)$; and `hsmooth`, that the closed point of $u_\kappa$ is not in the image of the first component map, so the section meets the special fibre at a point of the zeroth component only.
--
--   Set $X_{\overline{\mathbf Q}} :=$ the base change of `toBase p (ΓM M H) hj` along $R_p \to \overline{\mathbf Q}$, let $\mathrm{pr}_A : X_{\overline{\mathbf Q}} \to X_A :=$ `XO (ΓM M H) hj ρ` be the map of pullbacks induced by $A \hookrightarrow \overline{\mathbf Q}$, let `bcA` be the base-change map of the special fibre into $X_A$, and let $x_0 :=$ `bcA` applied to the closed point of $u_\kappa$. The assertion is: for every specialisation $\mathrm{hsp}$ of the image under $\mathrm{pr}_A \circ$ `eeta` of the generic point of `Meta.C` to $x_0$, and with
--   $$\mathrm{emb} : \mathcal O_{X_A, x_0} \to F$$
--   the ring homomorphism obtained by composing the specialisation map on stalks with the stalk maps of $\mathrm{pr}_A$ and of `eeta` at the generic point and then with `Meta.ffEquiv.symm`, there exist an element $t \in F$, a function $c$ from places of $F$ over $\overline{\mathbf Q}$ to $A$, and a ring homomorphism $\Phi$ from the image subring $\mathrm{emb}(\mathcal O_{X_A,x_0})$ to $A[[X]]$, such that all of the following hold.
--
--   First, $t$ lies in the valuation subring $R_1.\mathrm{integers}$. Second, for every place $W$ of $F$ which is strict of the first kind and satisfies $\mathrm{red}_1(W) = \mathrm{red}_1(Q)$, the value $c(W)$ lies in the maximal ideal of $A$ and $\mathrm{ord}_W\bigl(t - c(W)\bigr) = 1$, where $c(W)$ is viewed in $F$ through $\overline{\mathbf Q} \to F$ and $\mathrm{ord}$ is the normalised order of the place. Third, $c$ is injective on that family: if $W, W'$ are both strict of the first kind with $\mathrm{red}_1(W) = \mathrm{red}_1(W') = \mathrm{red}_1(Q)$ and $c(W) = c(W')$, then $W = W'$.
--
--   Fourth, $\Phi$ sends constants to constants: for $x \in A$ whose image in $F$ lies in the range of $\mathrm{emb}$, $\Phi$ of that element is the constant power series $x$. Fifth, if $t - c(Q)$ lies in the range of $\mathrm{emb}$, then $\Phi(t - c(Q)) = X$.
--
--   Sixth, the Taylor property: for every $f$ in the range of $\mathrm{emb}$ and every $k \in \mathbf N$ there is an element $r$ of the valuation subring of $Q$ with
--   $$f - \sum_{i<k} \mathrm{coeff}_i(\Phi f)\,\bigl(t - c(Q)\bigr)^i = \bigl(t - c(Q)\bigr)^k\, r,$$
--   the coefficients being transported from $A$ to $F$ via $\overline{\mathbf Q}$.
--
--   Seventh, the reduction law: for $f$ in the range of $\mathrm{emb}$ which moreover lies in $R_1.\mathrm{integers}$, and for $k \in \mathbf N$ such that $\mathrm{coeff}_i(\Phi f)$ lies in the maximal ideal of $A$ for all $i < k$ while $\mathrm{coeff}_k(\Phi f)$ does not, the residue $R_1.\mathrm{residue}(f) \in \bar F$ is non-zero and its order at the place $\mathrm{red}_1(Q)$ equals $k$.
--
--   Eighth, the converse direction: for $f$ in the range of $\mathrm{emb}$ lying in $R_1.\mathrm{integers}$ with $R_1.\mathrm{residue}(f) \neq 0$, some coefficient $\mathrm{coeff}_k(\Phi f)$ is a unit of $A$, that is, lies outside the maximal ideal.
--
--   This is the residue-disc (Taylor) expansion of germs of functions on the integral model $X_A$ at a smooth point $x_0$ of its special fibre met by the $A$-section attached to a place $Q$ that is strict of the first kind: it produces a parameter $t$ on the disc, the values of that parameter at the other strict places of the first kind reducing to the same place, and a coefficient homomorphism into $A[[X]]$ whose first unit coefficient computes the order of vanishing of the reduction. It feeds the statement [`ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict`](thm.html#ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict), within the analysis of $X_H$ over $\mathbf Z_p$ at level divisible by $p$ exactly once that underlies the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst
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

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceFst α hα Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 1).base) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl

    letI x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    ∀ (hsp : prA.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x₀),
    letI emb : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prA.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))
    ∃ (t : ↥(xHFunctionFieldBar M H)) (c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ↥A) (Φ : ↥(emb.range) →+* PowerSeries ↥A),

        t ∈ Rpd.R₁.integers ∧
        (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q →
          c W ∈ maximalIdeal ↥A ∧ W.ord (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c W : AlgebraicClosure ℚ)) = 1) ∧
        (∀ W W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W' → Psp.reduceFst α hα W' = Psp.reduceFst α hα Q →
          c W = c W' → W = W') ∧

        (∀ (x : ↥A) (hx : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (x : AlgebraicClosure ℚ) ∈ emb.range), Φ ⟨_, hx⟩ = PowerSeries.C x) ∧
        (∀ ht : t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ) ∈ emb.range, Φ ⟨_, ht⟩ = PowerSeries.X) ∧

        (∀ (f : ↥(emb.range)) (k : ℕ), ∃ r ∈ Q.toValuationSubring,
          (f : ↥(xHFunctionFieldBar M H)) - ∑ i ∈ Finset.range k, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((PowerSeries.coeff i (Φ f) : ↥A) : AlgebraicClosure ℚ) *
              (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ i =
            (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ k * r) ∧

        (∀ (f : ↥(emb.range)) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers) (k : ℕ),
          (∀ i < k, PowerSeries.coeff i (Φ f) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A →
          Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 ∧
            (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨f, hf⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = k) ∧
        (∀ (f : ↥(emb.range)) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          ∃ k, PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A) := by sorry
