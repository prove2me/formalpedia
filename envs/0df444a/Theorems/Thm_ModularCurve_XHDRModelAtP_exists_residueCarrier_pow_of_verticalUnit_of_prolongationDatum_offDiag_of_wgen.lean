-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_residueCarrier_pow_of_verticalUnit_of_prolongationDatum_offDiag_of_wgen
-- name    : ModularCurve.XHDRModelAtP.exists_residueCarrier_pow_of_verticalUnit_of_prolongationDatum_offDiag_of_wgen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/fb0ef5bd-476b-563f-9f00-30bac010fc51
-- title:
--   Band of residue carriers from a vertical unit
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), $H \le (\mathbb{Z}/M)^\times$ is a subgroup containing the whole kernel of the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ (`hHp`), and `hj` records that $j$, as a $q$-expansion, lies in the full-level $q$-expansion field over $\mathbb{Q}$. The geometric input is a model structure $\mathfrak{X} :$ `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over the base ring `R p`, which carries in particular a curve model $\mathfrak{X}.\mathrm{Meta}$ of $F_M :=$ `xHFunctionFieldBar M H` (the base change to $\overline{\mathbb{Q}}$, inside Laurent series, of the function field of $X_H(M)$ over $\mathbb{Q}$) together with the identification `eeta` of its underlying scheme with the geometric generic fibre, and the involution $\mathfrak{X}.w$.
--
--   Arithmetic data: a valuation subring $A \subset \overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA`, i.e. `A.LiesOverPrime p`), whose residue field $\kappa :=$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed; a ring homomorphism $\rho :$ `R p` $\to A$ whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structural map (`hρ`). Write $\bar{F} :=$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ at level `ΓN p M H hpM`, and $\varphi :=$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` for the restriction-along-Frobenius operation on places of $\bar{F}$.
--
--   Diamond data: a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue class is $p$ (`hpb`), and a map $\delta$ on the places of $\bar{F}$ which, by `hδ`, is the action of the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) pb)`. Node data: a finite set $SS$ of pairs of places of $\bar{F}$ which, by `hSS`, consists exactly of the elements of `ssNodePairsQExp κ (ΓN p M H hpM) p`, i.e. of the pairs $s$ with $s.2$ a supersingular place and $s.1 = \varphi(s.2)$.
--
--   Correspondence and specialisation data: an algebra automorphism $\theta$ of $F_M$ over $\overline{\mathbb{Q}}$; an $\overline{\mathbb{Q}}$-algebra map $\alpha$ from $F_{M/p} :=$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` to $F_M$, integral (`hα`), with $\theta \circ \alpha$ also integral (`hβ`); a place-specialisation structure $Psp$ for $X_H(M)$ at $A$, giving a surjective map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$ compatible with divisors of functions, inertia and Frobenius, and whence the two readings $V \mapsto \mathrm{sp}(V|_\alpha) =$ `Psp.reduceFst α hα V` and $V \mapsto \delta(\mathrm{sp}(V|_{\theta\circ\alpha})) =$ `Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V`; and a prolongation datum $Rpd$ for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ in $F_M$ with residue maps onto $\bar F$, with $f \in R_2$ if and only if $\theta f \in R_1$ and matching residues, and with $R_1$-residues of integral Laurent series computed coefficientwise.
--
--   The structural hypotheses on these data, all of them assumed, are: `hwgen`, that for any two sections $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ whose images in the generic fibre differ by $\mathfrak{X}.w$, the associated places satisfy $\mathrm{pointEquivPlace}(y') = \theta \cdot \mathrm{pointEquivPlace}(y)$; `hα_coe` and `hβ_coe`, the $q$-expansion pins stating that $\alpha$ is the identity on underlying Laurent series and that $\theta \circ \alpha$ acts on them by `qExpand` at $p$ (that is, $q \mapsto q^p$); `hθgal`, that $\theta$ commutes with the arithmetic Galois action of $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ on $F_M$; `hTD`, the type dichotomy, that every place $V$ of $F_M$ satisfies $\mathrm{reduceFst}(V) = \varphi(\mathrm{reduceSnd}(V))$ or $\delta(\varphi(\mathrm{reduceFst}(V))) = \mathrm{reduceSnd}(V)$; `hmodel`, that $Rpd$ is a model for $(\alpha, \theta\circ\alpha, \delta)$, i.e. the two divisor laws together with the two cusp-family laws at $\infty$ and at $0$; `hO`, the order law at $\delta$-fixed affine places; `hRL`, the regularity law relative to $SS$; and `hNV`, the node-value law relative to $SS$.
--
--   Two reduction-compatibility hypotheses, `hcompat` and `hcompat'`, are imposed in the following common situation: an index $i \in \{0,1\}$, a section $y$ of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$, an $A$-point $u$ of the model over $\mathrm{Spec}\,\rho$ whose generic restriction along `barPt A` is the image of $y$ in the generic fibre, a $\kappa$-point $u_\kappa$ of the fibre over `(residue A) ∘ ρ` which is a section of the fibre projection and reduces $u$, and a closed point $P_0$ of the curve $(\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ whose image under `efib` followed by the $i$-th component map is the closed point of $u_\kappa$. Under these conditions `hcompat` asserts that the place of $\bar F$ attached to $P_0$ by the fibre curve model equals $\mathrm{reduceFst}(\mathrm{pointEquivPlace}(y))$ when $i = 0$ and $\mathrm{reduceSnd}(\mathrm{pointEquivPlace}(y))$ when $i = 1$; and `hcompat'` asserts, in the same situation, that for $i = 0$ one has $\mathrm{reduceSnd}(\mathrm{pointEquivPlace}(y)) = \delta(\varphi(\text{place of } P_0))$, while for $i = 1$ one has $\mathrm{reduceFst}(\mathrm{pointEquivPlace}(y)) = \varphi(\text{place of } P_0)$.
--
--   Finally, the vertical-unit package: an element $G \in F_M$, a natural number $m$, a scalar $c \in \overline{\mathbb{Q}}$, a finite set $S_0 \subset \kappa$, a multiplicity function $n : \kappa \to \mathbb{N}$ and an element $e \in \kappa$, subject to: `hG₁`, $G \in R_1$; `hc`, $c \neq 0$ and $A.\mathrm{valuation}(c) < 1$; `hGres`, that $e \neq 0$, that every $a \in S_0$ lies in `ssJSet p κ` (every elliptic Weierstrass curve over $\kappa$ with $j$-invariant $a$ has no nonzero $p$-torsion point), that $\sum_{a \in S_0} n(a) = m$, and that for every $\bar{x} \in \bar{F}$ whose Laurent expansion is `jqModC κ` the $R_1$-residue of $G$ equals $e \prod_{a \in S_0} (\bar{x} - a)^{n(a)}$; `hθG`, $\theta(G) = c\,G^{-1}$; `hGY`, $\mathrm{ord}_V(G) = 0$ for every place $V$ of $F_M$ which is not cuspidal in the sense of `JHPlaceSpecialization.IsCuspidal` (i.e. $\mathrm{ord}_V(x - a) \le 0$ for all $a \in A$ and all $x$ with expansion `jqModC`); `hGinf`, that for every $x$ with expansion `jqModC (AlgebraicClosure ℚ)` and every place $C$ on the infinity side one has $\mathrm{ord}_C(G) = m\,\mathrm{ord}_C(x)$; and `hGzero`, that for every $x'$ with expansion `qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))` and every place $C$ on the zero side one has $\mathrm{ord}_C(G) = -m\,\mathrm{ord}_C(x')$.
--
--   The conclusion is the existence of a natural number $N$ with $N > 0$ such that for every $\varpi \in \overline{\mathbb{Q}}$ lying in the open band $A.\mathrm{valuation}(c) < A.\mathrm{valuation}(\varpi) < 1$ there exists $h \in F_M$ with the following four properties: $h \neq 0$; $h$ lies in $R_1$ and its $R_1$-residue is nonzero; the element $(\varpi^N)^{-1} h$ (the inverse being taken of the image of $\varpi^N$ in $F_M$) lies in $R_2$ and its $R_2$-residue is nonzero; and for every place $V$ of $F_M$ with $\mathrm{ord}_V(h) \neq 0$ which is neither strict of the first kind nor strict of the second kind — that is, for which neither $\delta(\varphi(\mathrm{reduceFst}(V))) = \mathrm{reduceSnd}(V)$ with $\mathrm{reduceFst}(V)$ not satisfying the predicate `JHPlaceSpecialization.Fixed` for $\delta$, nor $\mathrm{reduceFst}(V) = \varphi(\mathrm{reduceSnd}(V))$ with $\mathrm{reduceSnd}(V)$ not satisfying that predicate — there exists $s \in SS$ with $\mathrm{reduceFst}(V) = s.1$.
--
--   This is the construction step which converts a single vertical unit $G$ on the special fibre of the model of $X_H(M)$ at a prime $p$ exactly dividing $M$ into a whole band of functions: for each $\varpi$ whose valuation lies strictly between that of $c$ and $1$, a function which is a unit of the first Gauss prolongation, is $\varpi^N$ times a unit of the second, and whose divisor is supported, away from the strict places, over the supersingular node pairs. It is used by [`ModularCurve.XHDRModelAtP.exists_residueCarrier_of_ne_zero_of_prolongationDatum_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_residueCarrier_of_ne_zero_of_prolongationDatum_offDiag_of_wgen), and builds on the support statement [`ModularCurve.XHDRModelAtP.exists_mem_reduceFst_eq_of_ord_ne_zero_of_mul_commonUnit_of_ord_nonneg_of_ord_residue_eq_zero_of_prolongationDatum_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_mem_reduceFst_eq_of_ord_ne_zero_of_mul_commonUnit_of_ord_nonneg_of_ord_residue_eq_zero_of_prolongationDatum_offDiag_of_wgen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_residueCarrier_pow_of_verticalUnit_of_prolongationDatum_offDiag_of_wgen.lean

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

theorem ModularCurve.XHDRModelAtP.exists_residueCarrier_pow_of_verticalUnit_of_prolongationDatum_offDiag_of_wgen
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

    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)

    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (G : ↥(xHFunctionFieldBar M H)) (m : ℕ) (c : AlgebraicClosure ℚ) (S₀ : Finset (ResidueField ↥A)) (n : ResidueField ↥A → ℕ) (e : ResidueField ↥A)
    (hG₁ : G ∈ Rpd.R₁.integers)
    (hc : c ≠ 0 ∧ A.valuation c < 1)
    (hGres : e ≠ 0 ∧ (∀ a ∈ S₀, a ∈ @ssJSet p (ResidueField ↥A) _ (Classical.decEq _)) ∧ (∑ a ∈ S₀, n a = m) ∧
      ∀ xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) →
        Rpd.R₁.residue ⟨G, hG₁⟩ =
          algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) e * ∏ a ∈ S₀, (xb - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) a) ^ n a)
    (hθG : θ G = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c * G⁻¹)
    (hGY : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), ¬ JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V → V.ord G = 0)
    (hGinf : ∀ x : ↥(xHFunctionFieldBar M H), ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
      ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C → C.ord G = (m : ℤ) * C.ord x)
    (hGzero : ∀ x' : ↥(xHFunctionFieldBar M H), ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) →
      ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C → C.ord G = -((m : ℤ) * C.ord x')) :
    ∃ N : ℕ, 0 < N ∧
      ∀ ϖ : AlgebraicClosure ℚ, A.valuation c < A.valuation ϖ → A.valuation ϖ < 1 →
        ∃ h : ↥(xHFunctionFieldBar M H), h ≠ 0 ∧
          (∃ h₁ : h ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨h, h₁⟩ ≠ 0) ∧
          (∃ h₂ : (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (ϖ ^ N))⁻¹ * h ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨_, h₂⟩ ≠ 0) ∧
          (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            V.ord h ≠ 0 → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V →
              ∃ s ∈ SS, Psp.reduceFst α hα V = s.1) := by sorry
