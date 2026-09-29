-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd
-- name    : ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/b132c702-34cb-5f5f-99ab-aa26d8279cd6
-- title:
--   Residue-disc expansion of germs at strict places of the second kind
-- statement:
--   Throughout, $p$ is a prime, $M$ a positive integer with $p \mid M$ and $p^2 \nmid M$, and $H \le (\mathbb Z/M)^\times$ a subgroup containing every unit $u$ with $\mathrm{unitsMap}\,u = 1$ for the reduction $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$ (hypothesis `hHp`); `hj` records that the $q$-expansion $j$-series `jqModC ℚ` lies in the full-level $q$-expansion function field over $\mathbb Q$, and $\mathfrak X$ is an `XHDRModelAtP p M H hpM hj`, i.e. a model of $X_H$ over $R_p$ at $p$ together with its curve model $\mathfrak X.\mathrm{Meta}$ over $\overline{\mathbb Q}$ with function field $F :=$ `xHFunctionFieldBar M H`, the isomorphism $\mathfrak X.\mathtt{eeta}$ onto the base change of `toBase` to $\overline{\mathbb Q}$, and the remaining structure of that notion.
--
--   Arithmetic data. $A$ is a valuation subring of $\overline{\mathbb Q}$ lying over $p$ (that is, $p$ is a non-unit of $A$), with algebraically closed residue field $\kappa :=$ `ResidueField ↥A` of characteristic $p$, and $\rho : R_p \to A$ is a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb Q}$ is the structural map $R_p \to \overline{\mathbb Q}$ (`hρ`). Write $\bar F :=$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ at level $\Gamma_N(p,M,H)$.
--
--   The diamond operator. $pb$ is a unit of $\mathbb Z/(M/p)$ whose underlying residue is $p$ (`hpb`), and $\delta$ is a self-map of the set of places of $\bar F$ over $\kappa$ which, by `hδ`, acts as the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36).
--
--   The node pairs. $SS$ is a finset of pairs of places of $\bar F$ whose members are exactly the elements of `ssNodePairsQExp κ (ΓN p M H hpM) p`, i.e. those pairs $(w_1,w_2)$ with $w_2$ supersingular and $w_1$ the mod-$p$ Frobenius place of $w_2$ (`hSS`).
--
--   Correspondence data. $\theta$ is an automorphism of $F$ over $\overline{\mathbb Q}$; $\alpha$ is a $\overline{\mathbb Q}$-algebra homomorphism from $F' :=$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` into $F$, integral (`hα`), and the composite $\beta := \theta \circ \alpha$ is integral as well (`hβ`). Hypothesis `hα_coe` states that $\alpha$ is the identity on underlying Laurent series.
--
--   Specialisation and prolongation. `Psp` is a `JHPlaceSpecialization p M H hpM A`, consisting of a map $\mathrm{sp}$ from places of $F'$ to places of $\bar F$ and an induced map on degree-zero divisor classes, subject to the compatibility clauses of that structure (divisor and $q$-expansion compatibility, surjectivity, inertia invariance, Frobenius equivariance, and compatibility on $\mathrm{Pic}^0$). For a place $W$ of $F$ one writes $\mathrm{red}_1(W) := \mathrm{sp}(W|_\alpha)$ and $\mathrm{red}_2(W) := \delta(\mathrm{sp}(W|_\beta))$, restriction being taken along $\alpha$ resp. $\beta$. `Rpd` is a `ProlongationDatum` for `Psp` and $\theta$: two regular prolongations $R_1, R_2$ of $A$ to $F$ with residue maps to $\bar F$, with $f \in R_2.\mathrm{integers} \iff \theta f \in R_1.\mathrm{integers}$ and $R_2$-residues computed as $R_1$-residues of $\theta f$.
--
--   Geometric compatibilities. `hwgen` states that for rational points $y,y'$ of $\mathfrak X.\mathrm{Meta}.C$ over $\overline{\mathbb Q}$, if $y'$ followed by $\mathtt{eeta}$, the first pullback projection and $\mathfrak X.\mathtt w$ agrees with $y$ followed by $\mathtt{eeta}$ and the first projection, then the associated places satisfy $\mathrm{pointEquivPlace}\,y' = (\text{ofAlgAut }\theta)\cdot \mathrm{pointEquivPlace}\,y$. `hTD` is the type dichotomy: for every place $W$ of $F$, either $\mathrm{red}_1(W)$ is the Frobenius place of $\mathrm{red}_2(W)$, or $\delta$ applied to the Frobenius place of $\mathrm{red}_1(W)$ equals $\mathrm{red}_2(W)$. `hmodel` is `Rpd.IsModel` for $\alpha,\beta,\delta$, the conjunction of the two divisor laws and the two cusp laws at $\infty$ and at $0$. Hypotheses `hcompat` and `hcompat'` concern, for each $i \in \{0,1\}$, a rational point $y$, an $A$-section $u$ of `toBase p (ΓM M H) hj` over $\mathrm{Spec}\,\rho$ whose geometric fibre is $y$, a section $u_\kappa$ of the residue-field fibre compatible with $u$ and with the projection to the base, and a closed point $P_0$ of the special-fibre curve model $\mathfrak X.\mathrm{Mfib}$ whose image under $\mathtt{efib}$ followed by the $i$-th component map is the closed point of $u_\kappa$: `hcompat` asserts that the place attached to $P_0$ is $\mathrm{red}_1(\mathrm{pointEquivPlace}\,y)$ when $i=0$ and $\mathrm{red}_2(\mathrm{pointEquivPlace}\,y)$ when $i=1$, while `hcompat'` asserts the crossed identities: for $i=0$, $\mathrm{red}_2(\mathrm{pointEquivPlace}\,y) = \delta$ of the mod-$p$ Frobenius place of the place of $P_0$, and for $i=1$, $\mathrm{red}_1(\mathrm{pointEquivPlace}\,y)$ is the mod-$p$ Frobenius place of the place of $P_0$.
--
--   The place under consideration. $Q$ is a place of $F$ over $\overline{\mathbb Q}$ which is strict of the second kind, `Psp.IsStrictSnd`: $\mathrm{red}_1(Q)$ is the mod-$p$ Frobenius place of $\mathrm{red}_2(Q)$ and the predicate `Fixed` for $\delta$ fails at $\mathrm{red}_2(Q)$. Further, $u$ is an $A$-section over $\mathrm{Spec}\,\rho$ whose geometric point is the point of $\mathfrak X.\mathrm{Meta}.C$ corresponding to $Q$ (`hu`), $u_\kappa$ is a section of the residue-field fibre with $u_\kappa$ followed by the first projection equal to the reduction of $u$ (`huκ₁`) and followed by the second projection equal to the identity (`huκ₂`), and $P_0$ is a closed point of $\mathfrak X.\mathrm{Mfib}$ lying, via $\mathtt{efib}$ and the component map with index $1$, over the closed point of $u_\kappa$ (`hP0`), with attached place $\mathrm{red}_2(Q)$ (`hP0Q`); finally `hsmooth` requires that the closed point of $u_\kappa$ is not in the image of the component map with index $0$.
--
--   Set $X_{\overline{\mathbb Q}}$ for the base change of `toBase p (ΓM M H) hj` along $R_p \to \overline{\mathbb Q}$, let $\mathrm{prA} : X_{\overline{\mathbb Q}} \to X_A :=$ `XO (ΓM M H) hj ρ` be the map of pullbacks induced by $A \hookrightarrow \overline{\mathbb Q}$, let $\mathrm{bcA}$ be the base-change map from the residue-field fibre to $X_A$, and put $x_0 := \mathrm{bcA}$ applied to the closed point of $u_\kappa$.
--
--   Conclusion. For every specialisation relation $\mathrm{hsp}$ expressing that the image under $\mathrm{prA}$ of the image under $\mathtt{eeta}$ of the generic point of $\mathfrak X.\mathrm{Meta}.C$ specialises to $x_0$, consider the ring homomorphism $\mathrm{emb}$ from the stalk of $X_A$ at $x_0$ to $F$ given by the specialisation map `stalkSpecializes hsp`, followed by the stalk map of $\mathrm{prA}$ at $\mathtt{eeta}$ of the generic point, followed by the stalk map of $\mathtt{eeta}$ at the generic point, followed by $\mathrm{ffEquiv}^{-1}$ identifying the function field of $\mathfrak X.\mathrm{Meta}.C$ with $F$. Then there exist an element $t \in F$, a function $c$ from places of $F$ over $\overline{\mathbb Q}$ to $A$, and a ring homomorphism $\Phi$ from the range of $\mathrm{emb}$ to $A[[X]]$ such that:
--
--   (i) $t$ lies in $R_2.\mathrm{integers}$;
--
--   (ii) for every place $W$ of $F$ which is strict of the second kind and satisfies $\mathrm{red}_2(W) = \mathrm{red}_2(Q)$, the value $c(W)$ lies in the maximal ideal of $A$ and $\mathrm{ord}_W\bigl(t - c(W)\bigr) = 1$, the image of $c(W)$ in $F$ being taken through $\overline{\mathbb Q}$;
--
--   (iii) for all places $W, W'$ of $F$ that are strict of the second kind with $\mathrm{red}_2(W) = \mathrm{red}_2(W') = \mathrm{red}_2(Q)$, the equality $c(W) = c(W')$ forces $W = W'$;
--
--   (iv) for every $x \in A$ whose image in $F$ lies in the range of $\mathrm{emb}$, $\Phi$ of that element is the constant series $C(x)$;
--
--   (v) if $t - c(Q)$ lies in the range of $\mathrm{emb}$, then $\Phi$ sends it to $X$;
--
--   (vi) (Taylor property) for every $f$ in the range of $\mathrm{emb}$ and every $k \in \mathbb N$ there exists $r$ in the valuation ring of $Q$ with
--   $$f - \sum_{i<k} \mathrm{coeff}_i(\Phi f)\,\bigl(t - c(Q)\bigr)^i = \bigl(t - c(Q)\bigr)^k r,$$
--   the coefficients being viewed in $F$ through $A \subset \overline{\mathbb Q}$;
--
--   (vii) (reduction law) for every $f$ in the range of $\mathrm{emb}$ whose underlying element of $F$ lies in $R_2.\mathrm{integers}$ and every $k$ such that $\mathrm{coeff}_i(\Phi f)$ lies in the maximal ideal of $A$ for all $i < k$ while $\mathrm{coeff}_k(\Phi f)$ does not, the $R_2$-residue of $f$ is non-zero and its order at $\mathrm{red}_2(Q)$ equals $k$;
--
--   (viii) conversely, for every $f$ in the range of $\mathrm{emb}$ lying in $R_2.\mathrm{integers}$ with non-zero $R_2$-residue, some coefficient $\mathrm{coeff}_k(\Phi f)$ is a unit, i.e. lies outside the maximal ideal of $A$.
--
--   This is the residue-disc expansion of germs at a smooth point of the special fibre lying on the second of the two components of the Deligne–Rapoport model of $X_H$ at $p$: a local parameter $t$ with prescribed values $c(W)$ along the strict places of the second kind above $\mathrm{red}_2(Q)$, an $A$-integral Taylor homomorphism $\Phi$ into $A[[X]]$, and the dictionary between the first unit Taylor coefficient and the order of vanishing of the reduction. It is used in the construction of the Taylor expansion and order formula for germs at strict places, the step which converts local information on the arithmetic surface into orders of vanishing on the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd.lean

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

theorem ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd
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

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base) :
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

        t ∈ Rpd.R₂.integers ∧
        (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q →
          c W ∈ maximalIdeal ↥A ∧ W.ord (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c W : AlgebraicClosure ℚ)) = 1) ∧
        (∀ W W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W' → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q →
          c W = c W' → W = W') ∧

        (∀ (x : ↥A) (hx : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (x : AlgebraicClosure ℚ) ∈ emb.range), Φ ⟨_, hx⟩ = PowerSeries.C x) ∧
        (∀ ht : t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ) ∈ emb.range, Φ ⟨_, ht⟩ = PowerSeries.X) ∧

        (∀ (f : ↥(emb.range)) (k : ℕ), ∃ r ∈ Q.toValuationSubring,
          (f : ↥(xHFunctionFieldBar M H)) - ∑ i ∈ Finset.range k, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((PowerSeries.coeff i (Φ f) : ↥A) : AlgebraicClosure ℚ) *
              (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ i =
            (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ k * r) ∧

        (∀ (f : ↥(emb.range)) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₂.integers) (k : ℕ),
          (∀ i < k, PowerSeries.coeff i (Φ f) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A →
          Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 ∧
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨f, hf⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = k) ∧
        (∀ (f : ↥(emb.range)) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          ∃ k, PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A) := by sorry
