-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict
-- name    : ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/058082b2-5f8a-5ccd-bdba-a225f0e683ed
-- title:
--   Integral Taylor expansions on residue discs of strict places
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$ (hypothesis `hHp`), and $M/p$ nonzero. Let `hj` assert that the $q$-expansion $j(q)$, `jqModC ℚ`, lies in the $q$-expansion function field of full level over $\mathbb{Q}$, and let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`: a model of $X_H(M)$ over $R_p$ with the properties recorded in that structure, including a curve model $\mathfrak{X}.\mathtt{Meta}$ over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with function field $FM :=$ `xHFunctionFieldBar M H`, an isomorphism $\mathfrak{X}.\mathtt{eeta}$ onto the base change of the model to $\overline{\mathbb{Q}}$, and the bijection $\mathfrak{X}.\mathtt{Meta.pointEquivPlace}$ between $\overline{\mathbb{Q}}$-sections of $\mathfrak{X}.\mathtt{Meta.toBase}$ and places of $FM$ over $\overline{\mathbb{Q}}$.
--
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA : A.LiesOverPrime p`), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, and let $\rho : R_p \to A$ satisfy $A.\mathtt{subtype} \circ \rho =$ the structure map $R_p \to \overline{\mathbb{Q}}$ (hypothesis `hρ`). Write $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field of level $\Gamma_N(p,M,H)$ over $\kappa$, and $FMp$ for `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, where `infSubgroup` is the image of $H$ in $(\mathbb{Z}/(M/p))^\times$.
--
--   The remaining data are: a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$; a self-map $\delta$ of the set of places of $\bar F$ over $\kappa$ which, by `hδ`, is the action of the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36); a finite set $SS$ of pairs of places of $\bar F$ whose members are, by `hSS`, exactly the pairs $(s_1,s_2)$ with $s_2$ supersingular and $s_1$ the modular Frobenius image of $s_2$ (`ssNodePairsQExp`); an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $FM$; an $\overline{\mathbb{Q}}$-algebra map $\alpha : FMp \to FM$, integral by `hα`, with $\beta := \theta \circ \alpha$ integral by `hβ`; a place-specialisation datum $Psp$ of type `JHPlaceSpecialization p M H hpM A` (a map $\mathrm{sp}$ from places of $FMp$ to places of $\bar F$ together with a map on degree-zero divisor classes, surjectivity of $\mathrm{sp}$, compatibility with $q$-expansion divisors, inertia invariance, Frobenius equivariance and compatibility on $\mathrm{Pic}^0$); and a prolongation datum $Rpd$ for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $FM$ with residue maps to $\bar F$, the compatibility of $R_1$ with reading Laurent coefficients, and the identification of $R_2$ with the $\theta$-transport of $R_1$.
--
--   The further hypotheses are: `hwgen`, that for two $\overline{\mathbb{Q}}$-sections $y, y'$ of $\mathfrak{X}.\mathtt{Meta.toBase}$, if $y'$ followed by $\mathfrak{X}.\mathtt{eeta}$, the first pullback projection and $\mathfrak{X}.\mathtt{w}$ agrees with $y$ followed by $\mathfrak{X}.\mathtt{eeta}$ and the first projection, then the place of $y'$ is the image of the place of $y$ under the semilinear automorphism attached to $\theta$; `hα_coe`, that $\alpha$ does not change underlying Laurent series; `hTD`, the type dichotomy for $(\alpha,\beta,\delta)$, namely that every place $W$ of $FM$ satisfies $\mathrm{red}_1(W) = \mathrm{Frob}(\mathrm{red}_2(W))$ or $\delta(\mathrm{Frob}(\mathrm{red}_1(W))) = \mathrm{red}_2(W)$, where $\mathrm{red}_1(W) := Psp.\mathtt{reduceFst}\,\alpha\,h\alpha\,W = \mathrm{sp}(W|_\alpha)$, $\mathrm{red}_2(W) := Psp.\mathtt{reduceSnd}\,\beta\,h\beta\,\delta\,W = \delta(\mathrm{sp}(W|_\beta))$ and $\mathrm{Frob}$ is `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`; and `hmodel`, that $Rpd$ is a model for $(\alpha,\beta,\delta)$, that is, the two divisor laws together with the two cusp laws hold. Finally, two compatibility hypotheses `hcompat` and `hcompat'` are imposed, with the same binders: for each index $i \in \{0,1\}$, each $\overline{\mathbb{Q}}$-section $y$ of $\mathfrak{X}.\mathtt{Meta.toBase}$, each point $u$ of the model over $\mathrm{Spec}\,\rho$ whose base change along $A \hookrightarrow \overline{\mathbb{Q}}$ is $y$ followed by $\mathfrak{X}.\mathtt{eeta}$ and the first projection, each $\kappa$-section $u\kappa$ of the fibre of the model at the composite $R_p \to A \to \kappa$ whose first projection is the reduction of $u$ and whose second projection is the identity, and each closed point $P_0$ of the curve model $\mathfrak{X}.\mathtt{Mfib}\,A\,hA\,\rho\,h\rho$ (whose places are places of $\bar F$ over $\kappa$) whose image under $\mathfrak{X}.\mathtt{efib}$ followed by $\mathfrak{X}.\mathtt{comp}\,A\,hA\,\rho\,h\rho\,i$ is the image of the closed point under $u\kappa$: the hypothesis `hcompat` requires that the place of $P_0$ equals $\mathrm{red}_1$ of the place of $y$ when $i = 0$ and $\mathrm{red}_2$ of the place of $y$ otherwise, while `hcompat'` requires that for $i = 0$ the place $\mathrm{red}_2$ of the place of $y$ equals $\delta(\mathrm{Frob}(\text{place of } P_0))$, and for $i = 1$ that $\mathrm{red}_1$ of the place of $y$ equals $\mathrm{Frob}(\text{place of } P_0)$.
--
--   The conclusion is a conjunction of two symmetric assertions, one for strict places of the first kind and one for strict places of the second kind.
--
--   First assertion. Let $Q$ be a place of $FM$ over $\overline{\mathbb{Q}}$ which is strict of the first kind, i.e. $\delta(\mathrm{Frob}(\mathrm{red}_1(Q))) = \mathrm{red}_2(Q)$ and $\mathrm{red}_1(Q)$ is not fixed in the sense of the predicate `Fixed` for $\delta$, and assume $\mathrm{red}_1(Q)$ is an affine place in the sense of `JHPlaceSpecialization.IsAffinePlace`, that is, there are $x \in \bar F$ whose Laurent series is `jqModC κ` and $a \in \kappa$ such that $x$ lies in the valuation ring of $\mathrm{red}_1(Q)$ with residue the image of $a$. Put
--   $$B := R_1.\mathtt{integers} \cap \bigcap_{W} \mathcal{O}_W \subseteq FM,$$
--   the intersection being over all places $W$ of $FM$ that are strict of the first kind with $\mathrm{red}_1(W) = \mathrm{red}_1(Q)$, and $\mathcal{O}_W$ the valuation subring of $W$. Then there exist $t \in FM$, a function $c$ from places of $FM$ to $A$, and a ring homomorphism $\Phi : B \to A[[X]]$ such that:
--
--   (i) $t$ lies in $R_1.\mathtt{integers}$;
--
--   (ii) for every place $W$ strict of the first kind with $\mathrm{red}_1(W) = \mathrm{red}_1(Q)$, the element $c(W)$ lies in the maximal ideal of $A$ and $\mathrm{ord}_W(t - c(W)) = 1$, where $c(W)$ is viewed in $FM$ through $\overline{\mathbb{Q}} \to FM$;
--
--   (iii) $c$ is injective on such places: if $W, W'$ are both strict of the first kind with $\mathrm{red}_1(W) = \mathrm{red}_1(W') = \mathrm{red}_1(Q)$ and $c(W) = c(W')$, then $W = W'$;
--
--   (iv) for every $x \in A$ whose image in $FM$ lies in $B$, $\Phi$ sends that image to the constant power series $x$;
--
--   (v) if $t - c(Q)$ lies in $B$, then $\Phi(t - c(Q)) = X$;
--
--   (vi) (Taylor approximation) for every $f \in B$ and every $k \in \mathbb{N}$ there is $r$ in the valuation ring of $Q$ with
--   $$f - \sum_{i < k} \mathrm{coeff}_i(\Phi f)\,(t - c(Q))^i = (t - c(Q))^k\, r,$$
--   the coefficients and $c(Q)$ being taken in $FM$ through $A \subseteq \overline{\mathbb{Q}} \to FM$;
--
--   (vii) for every $f \in B$ whose underlying element lies in $R_1.\mathtt{integers}$ and every $k$ such that $\mathrm{coeff}_i(\Phi f)$ lies in the maximal ideal of $A$ for all $i < k$ while $\mathrm{coeff}_k(\Phi f)$ does not, the residue $R_1.\mathtt{residue}(f) \in \bar F$ is nonzero and its order at $\mathrm{red}_1(Q)$ equals $k$;
--
--   (viii) conversely, for every $f \in B$ lying in $R_1.\mathtt{integers}$ with $R_1.\mathtt{residue}(f) \neq 0$ there exists $k$ with $\mathrm{coeff}_k(\Phi f)$ outside the maximal ideal of $A$.
--
--   Second assertion. The same statement with 'strict of the first kind' replaced by 'strict of the second kind' (that is, $\mathrm{red}_1(Q) = \mathrm{Frob}(\mathrm{red}_2(Q))$ and $\mathrm{red}_2(Q)$ is not fixed in the sense of `Fixed` for $\delta$), with $\mathrm{red}_1$ replaced throughout by $\mathrm{red}_2$ and $R_1$ by $R_2$: for every such $Q$ with $\mathrm{red}_2(Q)$ affine, and with $B := R_2.\mathtt{integers} \cap \bigcap_W \mathcal{O}_W$ over the places $W$ strict of the second kind with $\mathrm{red}_2(W) = \mathrm{red}_2(Q)$, there exist $t \in FM$, $c$ and $\Phi : B \to A[[X]]$ satisfying the eight clauses (i)–(viii) verbatim with $R_2$ and $\mathrm{red}_2$ in place of $R_1$ and $\mathrm{red}_1$.
--
--   This is the residue-disc dictionary on the model of $X_H(M)$ at a prime $p$ exactly dividing $M$: functions that are integral for one of the two Gauss prolongations and regular at all $\overline{\mathbb{Q}}$-points of a residue disc admit an $A$-integral Taylor expansion in a disc parameter, and the order of vanishing of the reduction is read off from the first coefficient outside the maximal ideal. It is used in [`ModularCurve.XHDRModelAtP.discLawFst_and_discLawSnd_of_jHPlaceSpecialization_of_offDiag`](thm.html#ModularCurve.XHDRModelAtP.discLawFst_and_discLawSnd_of_jHPlaceSpecialization_of_offDiag) to verify the two disc laws for a place-specialisation datum off the diagonal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict
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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    (∀ (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q →
      JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →

      letI B : Subring ↥(xHFunctionFieldBar M H) :=
        Rpd.R₁.integers.toSubring ⊓
          ⨅ W : {W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) // Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ Psp.reduceFst α hα W = Psp.reduceFst α hα Q}, W.1.toValuationSubring.toSubring
      ∃ (t : ↥(xHFunctionFieldBar M H)) (c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ↥A) (Φ : ↥B →+* PowerSeries ↥A),

        t ∈ Rpd.R₁.integers ∧
        (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q →
          c W ∈ maximalIdeal ↥A ∧ W.ord (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c W : AlgebraicClosure ℚ)) = 1) ∧
        (∀ W W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W' → Psp.reduceFst α hα W' = Psp.reduceFst α hα Q →
          c W = c W' → W = W') ∧

        (∀ (x : ↥A) (hx : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (x : AlgebraicClosure ℚ) ∈ B), Φ ⟨_, hx⟩ = PowerSeries.C x) ∧
        (∀ ht : t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ) ∈ B, Φ ⟨_, ht⟩ = PowerSeries.X) ∧

        (∀ (f : ↥B) (k : ℕ), ∃ r ∈ Q.toValuationSubring,
          (f : ↥(xHFunctionFieldBar M H)) - ∑ i ∈ Finset.range k, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((PowerSeries.coeff i (Φ f) : ↥A) : AlgebraicClosure ℚ) *
              (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ i =
            (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ k * r) ∧

        (∀ (f : ↥B) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers) (k : ℕ),
          (∀ i < k, PowerSeries.coeff i (Φ f) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A →
          Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 ∧
            (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨f, hf⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = k) ∧

        (∀ (f : ↥B) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          ∃ k, PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A)) ∧
    (∀ (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q →
      JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →

      letI B : Subring ↥(xHFunctionFieldBar M H) :=
        Rpd.R₂.integers.toSubring ⊓
          ⨅ W : {W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) // Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q}, W.1.toValuationSubring.toSubring
      ∃ (t : ↥(xHFunctionFieldBar M H)) (c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ↥A) (Φ : ↥B →+* PowerSeries ↥A),

        t ∈ Rpd.R₂.integers ∧
        (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q →
          c W ∈ maximalIdeal ↥A ∧ W.ord (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c W : AlgebraicClosure ℚ)) = 1) ∧
        (∀ W W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W' → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q →
          c W = c W' → W = W') ∧

        (∀ (x : ↥A) (hx : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (x : AlgebraicClosure ℚ) ∈ B), Φ ⟨_, hx⟩ = PowerSeries.C x) ∧
        (∀ ht : t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ) ∈ B, Φ ⟨_, ht⟩ = PowerSeries.X) ∧

        (∀ (f : ↥B) (k : ℕ), ∃ r ∈ Q.toValuationSubring,
          (f : ↥(xHFunctionFieldBar M H)) - ∑ i ∈ Finset.range k, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((PowerSeries.coeff i (Φ f) : ↥A) : AlgebraicClosure ℚ) *
              (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ i =
            (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ k * r) ∧

        (∀ (f : ↥B) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₂.integers) (k : ℕ),
          (∀ i < k, PowerSeries.coeff i (Φ f) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A →
          Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 ∧
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨f, hf⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = k) ∧

        (∀ (f : ↥B) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          ∃ k, PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A)) := by sorry
