-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_opens_sup_eq_top_and_forall_mem_basicOpen_of_crossingChart_of_sections
-- name    : ModularCurve.XHDRModelAtP.exists_opens_sup_eq_top_and_forall_mem_basicOpen_of_crossingChart_of_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/836e288b-2ba5-50cd-8395-baa6a73024e5
-- title:
--   Crossing chart and section complement cover X_A
-- statement:
--   Fix a prime $p$ and a nonzero $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis $hj$ that the $q$-series `jqModC ℚ` lies in the level-one $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`; let $\mathfrak{X}$ be a datum of type `XHDRModelAtP p M H hpM hj`, i.e. an integral model of $X_H$ over $R\,p$ with the properness, flatness, normality, smoothness and Galois-compatibility clauses of that structure. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`LiesOverPrime p`), whose residue field is algebraically closed of characteristic $p$, and let $\rho : R\,p \to A$ be a ring map compatible with $R\,p \to \overline{\mathbb{Q}}$. Write $\mathfrak{X}_A$ for `pullback (toBase p (ΓM M H) hj) (Spec.map ρ)`. Let $bc$ be a morphism from the fibre of the model over $\mathrm{res}\circ\rho$ (the special fibre) to $\mathfrak{X}_A$, let $n$ be a point of the pullback of the two morphisms `𝔛.comp A hA ρ hρ 0` and `𝔛.comp A hA ρ hρ 1` supplied by $\mathfrak{X}$, and let $x_n \in \mathfrak{X}_A$ denote its image under `pullback.fst _ _ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc`. Let $e \in \mathbb{N}$ and let $U \subseteq \mathfrak{X}_A$ be an open containing $x_n$, equipped with a morphism $f : U \to \operatorname{Spec}\bigl(A[X_0,X_1]/(X_0X_1 - (p)^e)\bigr) =$ `CrossingQuotient.crossingScheme ((p : A)^e)` which is a morphism over $\operatorname{Spec} A$, in the sense that $f$ followed by the map induced by $A \to A[X_0,X_1]/(X_0X_1-(p)^e)$ equals $U \hookrightarrow \mathfrak{X}_A \to \operatorname{Spec} A$; assume that for $y \in U$ the prime $f(y)$ contains both distinguished elements `CrossingQuotient.U ((p:A)^e)` and `CrossingQuotient.V ((p:A)^e)` exactly when $y$ maps to $x_n$, and that there is an open $W_{\mathrm{et}} \subseteq U$ containing a point over $x_n$ with $W_{\mathrm{et}} \hookrightarrow U \to$ chart étale. Let $x'y' = (p)^e$ and $x''y'' = (p)^e$ in $A$, and let $s, s' : \operatorname{Spec} A \to U$ be two sections of $U \to \operatorname{Spec} A$ whose closed points map to $x_n$, with $s$ followed by $f$ equal to the morphism induced by `CrossingQuotient.lift x' y'` and $s'$ followed by $f$ the one induced by `CrossingQuotient.lift x'' y''`, each assumed to be the unique section of $U \to \operatorname{Spec} A$ through $x_n$ with those chart values. Transporting $A[X_0,X_1]/(X_0X_1-(p)^e)$ to the global sections of the chart scheme $\mathrm{Mdl}$ along the inverse of `Scheme.ΓSpecIso`, put $a = U - x'$, $b = y' - V$, $a' = U - x''$, $b' = y'' - V$. The assertion is that there exist opens $W_2, W_3 \subseteq \mathfrak{X}_A$ with $W_2 \sqcup W_3 = \top$, $W_2 \le U$, $x_n \in W_2$, with $W_3$ consisting exactly of the points lying in neither the image of $s$ followed by $U \hookrightarrow \mathfrak{X}_A$ nor that of $s'$, and such that every $y \in U$ whose image lies in both $W_2$ and $W_3$ satisfies $f(y) \in (D(a) \cup D(b)) \cap (D(a') \cup D(b'))$ in $\mathrm{Mdl}$.
--
--   This is the covering step in the local analysis at a crossing point of the special fibre of the Deligne–Rapoport-type model $\mathfrak{X}_A$ of $X_H(M)$ with $p \parallel M$: the crossing chart neighbourhood and the complement of the two given $A$-sections through the crossing cover the model, and over the overlap the chart misses the two model sections cut out by $u - x'$, $y' - v$ and by $u - x''$, $y'' - v$. It is used in the construction comparing the ideal modules of the two sections near the crossing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_opens_sup_eq_top_and_forall_mem_basicOpen_of_crossingChart_of_sections.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing ModularCurve ModularCurve.XHDRLevel MvPolynomial
open scoped MatrixGroups

set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_opens_sup_eq_top_and_forall_mem_basicOpen_of_crossingChart_of_sections
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶
      pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ)
    (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : ↥A) ^ e))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e)))) =
      U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal ∧
        CrossingQuotient.V (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal) ↔
      U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n)
    (Wet : (U : Scheme.{0}).Opens)
    (hWet : ∃ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n ∧ y ∈ Wet)
    [AlgebraicGeometry.Etale (Wet.ι ≫ f)]

    (x' y' : ↥A) (hxy : x' * y' = algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e))
    (x'' y'' : ↥A) (hxy' : x'' * y'' = algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e))
    (sU sU' : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}))
    (hsU : sU ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _) (hsU' : sU' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _)

    (hsx : U.ι.base (sU.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n)
    (hsx' : U.ι.base (sU'.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n)
    (hfs : sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) x' y' hxy).toRingHom))
    (hfs' : sU' ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) x'' y'' hxy').toRingHom))
    (huniq : ∀ s₁ : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}), s₁ ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
      U.ι.base (s₁.base (IsLocalRing.closedPoint ↥A)) =
        (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n →
      s₁ ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) x' y' hxy).toRingHom) → s₁ = sU)
    (huniq' : ∀ s₁ : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}), s₁ ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
      U.ι.base (s₁.base (IsLocalRing.closedPoint ↥A)) =
        (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n →
      s₁ ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) x'' y'' hxy').toRingHom) → s₁ = sU') :
    letI Mdl : Scheme.{0} := CrossingQuotient.crossingScheme (((p : ℕ) : ↥A) ^ e)
    letI φ : CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e) →+* Γ(Mdl, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e)))).inv.hom
    letI a : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥A _ x')
    letI b : Γ(Mdl, ⊤) := φ (algebraMap ↥A _ y' - CrossingQuotient.V _)
    letI a' : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥A _ x'')
    letI b' : Γ(Mdl, ⊤) := φ (algebraMap ↥A _ y'' - CrossingQuotient.V _)
    ∃ W₂ W₃ : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens,
      W₂ ⊔ W₃ = ⊤ ∧ W₂ ≤ U ∧
      (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n ∈ W₂ ∧
      (∀ z, z ∈ W₃ ↔ (z ∉ Set.range (sU ≫ U.ι).base ∧ z ∉ Set.range (sU' ≫ U.ι).base)) ∧
      (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ W₂ → U.ι.base y ∈ W₃ →
        f.base y ∈ (Mdl.basicOpen a ⊔ Mdl.basicOpen b) ⊓ (Mdl.basicOpen a' ⊔ Mdl.basicOpen b')) := by sorry
