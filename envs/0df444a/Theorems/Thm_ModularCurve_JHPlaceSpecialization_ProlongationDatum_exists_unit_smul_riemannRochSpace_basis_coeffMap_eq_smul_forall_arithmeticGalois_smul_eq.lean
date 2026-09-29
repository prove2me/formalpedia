-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_unit_smul_riemannRochSpace_basis_coeffMap_eq_smul_forall_arithmeticGalois_smul_eq
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_unit_smul_riemannRochSpace_basis_coeffMap_eq_smul_forall_arithmeticGalois_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/da7c380a-45a9-5597-8f0e-9cca6d221d69
-- title:
--   Unit U with S-fixed bounded-denominator basis of U· L(D)
-- statement:
--   The setting is the specialisation of the modular curve $X_H(M)$ at a place of $\overline{\mathbb Q}$ above an exactly dividing prime.
--
--   Fixed data. A prime $p$ and a natural number $M$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`); a subgroup $H \le (\mathbb Z/M)^{\times}$ such that every unit of $\mathbb Z/M$ whose image under $\mathbb Z/M \to \mathbb Z/(M/p)$ is $1$ lies in $H$ (`hHp`); a valuation subring $A \subseteq \overline{\mathbb Q}$ with $p$ a non-unit of $A$ (`hA`), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $F_M = \overline{\mathbb Q}\cdot x_H(M)$ for the base change to $\overline{\mathbb Q}$ of the function field `xHFunctionField M H` inside Laurent series, $F_{M/p}$ for the corresponding field at level $M/p$ with the image subgroup `infSubgroup p M H hpM`, and $\bar F =$ `Fbar p M H hpM κ` for the mod-$p$ $q$-expansion function field of $\Gamma' =$ `ΓN p M H hpM` over $\kappa$. Further: a $\overline{\mathbb Q}$-algebra automorphism $\theta$ of $F_M$; an integral $\overline{\mathbb Q}$-algebra map $\alpha : F_{M/p} \to F_M$ (`hα`) which is the identity on $q$-expansions (`hα_coe`), with $\beta = \theta \circ \alpha$ integral (`hβ`); a unit $pb$ of $\mathbb Z/(M/p)$ reducing to $p$ (`hpb`); a self-map $\delta$ of the places of $\bar F$ over $\kappa$ given (`hδ`) by the semilinear action of the mod-$p$ diamond automorphism attached to a $\Gamma_0(M/p)$-lift of $pb$; a finite set $SS$ of pairs of places of $\bar F$ which is exactly the set of supersingular node pairs, i.e. pairs $s$ with $s.2$ supersingular and $s.1$ the $q$-expansion Frobenius image of $s.2$ (`hSS`); a place specialisation $Psp$ (a map $sp$ from places of $F_{M/p}$ to places of $\bar F$ together with a homomorphism on degree-zero divisor classes, subject to the axioms of `JHPlaceSpecialization`: compatibility of pushforward of principal divisors with reduction of $A$-integral $q$-expansions, surjectivity, invariance under inertia, transport of Frobenius elements to `qExpFrobeniusPlaceModL`, and compatibility of the class-group map with pushforward); and a prolongation datum $Rpd$ for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue field $\bar F$, such that $R_1$-residues compute the reduction of $A$-integral $q$-expansions, and $f \in R_2$ iff $\theta f \in R_1$, with $\mathrm{res}_2(f) = \mathrm{res}_1(\theta f)$. Throughout, $\mathrm{reduceFst}(W) = sp(W|_{\alpha})$ and $\mathrm{reduceSnd}(W) = \delta(sp(W|_{\beta}))$; a place $W$ of $F_M$ is strict of the first kind when $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ and $\mathrm{reduceFst}\,W$ is not $\delta$-fixed, strict of the second kind when $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ and $\mathrm{reduceSnd}\,W$ is not $\delta$-fixed, where a place $v$ of $\bar F$ is $\delta$-fixed when $\mathrm{Frob}(\delta(\mathrm{Frob}\,v)) = v$.
--
--   Structural hypotheses on the reduction. `hFix`: every supersingular place $y$ of $\bar F$ and its Frobenius image are $\delta$-fixed. `hTD`: every place of $F_M$ satisfies at least one of the two strictness equalities (type dichotomy). `hmodel`: $Rpd$ is a model for $\alpha, \beta, \delta$, i.e. the two divisor laws and the two cusp laws hold. `hO`: the order law at $\delta$-fixed affine places — for $f$ lying in both $R_1$ and $R_2$ with non-zero residues, the pushforward along $\mathrm{reduceFst}$ of $\mathrm{div}(f)$ at such a place $v$ is $\mathrm{ord}_v(\mathrm{res}_1 f) + \mathrm{ord}_{\delta(\mathrm{Frob}\,v)}(\mathrm{res}_2 f)$. `hreg`: the regularity law for $SS$ (non-negativity of the two residual orders at $\delta$-fixed affine places, and existence of a common value at node pairs, when $f$ has no poles above the place concerned). `hnv`: the node value law for $SS$ (a common non-zero value of the two residues at a node pair not met by the divisor of $f$). `hθgal`: $\theta$ commutes with the arithmetic Galois action of $\mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ on $F_M$. `hβ_coe`: the $q$-expansion of $\beta u$ is obtained from that of $u$ by $q \mapsto q^p$. `hFixFin`: the set of $\delta$-fixed places of $\bar F$ is finite.
--
--   Local pole hypotheses `hLFst` and `hLSnd`. `hLFst` requires: for all places $Q \neq Q'$ of $F_M$, both strict of the first kind, with the same image $\mathrm{reduceFst}\,Q' = \mathrm{reduceFst}\,Q$ which is an affine place of $\bar F$ (a place having a value at an element of $\bar F$ whose $q$-expansion is $j$), for every natural number $n$ with non-zero image in $\kappa$, for every $g \in R_1$ with non-zero $R_1$-residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict first-kind place $W$ with the same $\mathrm{reduceFst}$-image, and for all $e \in A$ and $\varepsilon \in R_1$ with non-zero $R_1$-residue such that $g = 1 + e\,\varepsilon$, the inequality $\mathrm{ord}_{\mathrm{reduceFst}\,Q}(\mathrm{res}_1 \varepsilon) \ge -1$ holds. `hLSnd` is the same statement with $\mathrm{reduceFst}$, strictness of the first kind and $R_1$ replaced by $\mathrm{reduceSnd}$, strictness of the second kind and $R_2$.
--
--   Uniformiser hypothesis `hUnit`. There exist $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ of $F_M$ with $D_1 = \mathrm{div}(u_1)$ and $D_2 = \mathrm{div}(u_2)$ place by place, such that: $u_1$ and $u_1^{-1}$ lie in $R_1$ with $\mathrm{res}_1(u_1) \neq 0$, the pushforward along $\mathrm{reduceFst}$ of the strict first-kind part of $D_1$ agrees at every non-$\delta$-fixed place $v$ with $\mathrm{ord}_v(\mathrm{res}_1 u_1)$, and the pushforward along $\mathrm{reduceFst}$ of the restriction of $D_1$ to the infinity-side places agrees, at $\mathrm{reduceFst}\,C$ for every infinity-side place $C$, with $\mathrm{ord}_{\mathrm{reduceFst}\,C}(\mathrm{res}_1 u_1)$; every non-zero $f \in F_M$ admits $m \neq 0$ in $\mathbb N$ and $j \in \mathbb Z$ with $f^m u_1^{\,j} \in R_2$ of non-zero $R_2$-residue; and the two symmetric clauses for $u_2$, with $R_2$, $\mathrm{reduceSnd}$, the strict second-kind part of $D_2$, the zero-side places, and the corresponding power condition landing in $R_1$. Here an infinity-side place is a cuspidal place having value a residue-$1$ element of $A$ at $x'/x^p$, where $x, x'$ have $q$-expansions $j$ and $j(q^p)$, and a zero-side place is a cuspidal place (in the second sense) having such a value at $x/x'^p$.
--
--   Cusp and orientation hypotheses. `hcusp`: every non-affine place $w$ of $\bar F$ is the $\mathrm{reduceFst}$-image of some infinity-side place and the $\mathrm{reduceSnd}$-image of some zero-side place. `horientInf`: for every infinity-side place $C$, $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,C)) = \mathrm{reduceSnd}\,C$. `horient0`: for every zero-side place $C$, $\mathrm{reduceFst}\,C = \mathrm{Frob}(\mathrm{reduceSnd}\,C)$.
--
--   Annulus hypotheses. A function $e : SS \to \mathbb N$ with $e(s) > 0$ for all $s$ (`he`), and `hAnn`: for each $s \in SS$ there is an annulus $An$ over $A$ in $F_M$ (a set $\mathrm{dom}$ of places, a parameter $\mathrm{param}$, a modulus in the maximal ideal of $A$, with the axioms of `Annulus`: rationality and smallness of the parameter's values on $\mathrm{dom}$, unique realisation of admissible values, order one of $\mathrm{param}$ minus its value, and the unit principle) such that $\mathrm{dom}$ consists exactly of the places $W$ with $\mathrm{reduceFst}\,W = s.1$ which are strict of neither kind; the modulus equals $p^{e(s)}$ times a unit of $A$; $\mathrm{param}$ is invariant under the arithmetic Galois action of every $\sigma$ in the inertia subgroup of $A$ over $\mathbb Q$; $\mathrm{modulus}^{-1}\,\mathrm{param} \in R_1$; $\mathrm{param} \in R_2$ with non-zero $R_2$-residue; the $R_2$-residue of $\mathrm{param}$ has order $1$ at $s.2$, and for every $f \in R_2$ with non-zero residue and no zeros or poles on $\mathrm{dom}$, the product of the value of $f$ and the value of $\mathrm{param}$ raised to $-\mathrm{ord}_{s.2}(\mathrm{res}_2 f)$ is a unit of $A$ at every place of $\mathrm{dom}$; and the symmetric clause for $\mathrm{modulus}\cdot \mathrm{param}^{-1} \in R_1$ at $s.1$ with $R_1$-residues.
--
--   Final data. A set $S$ of automorphisms of $\overline{\mathbb Q}$ over $\mathbb Q$ contained in the inertia subgroup of $A$ over $\mathbb Q$ (`hS`); an effective divisor $D \ge 0$ of $F_M$ (`hD`) which is good, in the sense that every place in its support is strict of the first or of the second kind (`hgood`), and each place in the support of $D$ is fixed by the arithmetic Galois action of every $\sigma \in S$ (`hDfix`); the Riemann–Roch space $L(D) = \{f : v(f) \le \exp(D v) \text{ for all } v\}$ is finite-dimensional over $\overline{\mathbb Q}$.
--
--   Conclusion. There exists $U \in F_M$ such that: $U$ lies in $R_1$ and is a unit of that valuation subring; $U$ lies in $R_2$ and is a unit of that valuation subring; $\sigma \cdot U = U$ for every $\sigma \in S$ under the arithmetic Galois action; and there exists a family $b$ indexed by $\mathrm{Fin}$ of the $\overline{\mathbb Q}$-dimension of the image $U\cdot L(D)$ of $L(D)$ under multiplication by $U$, such that each $b_i$ lies in $U \cdot L(D)$, the family $b$ is linearly independent over $\overline{\mathbb Q}$, for each $i$ there are a non-zero $c \in \overline{\mathbb Q}$ and a Laurent series $y$ with coefficients in $A$ whose image under the coefficientwise inclusion $A \hookrightarrow \overline{\mathbb Q}$ equals $c$ times the $q$-expansion of $b_i$, and likewise a non-zero constant and an $A$-integral Laurent series for the $q$-expansion of $\theta(b_i)$, and finally $\sigma \cdot b_i = b_i$ for every $i$ and every $\sigma \in S$.
--
--   This is the bounded-denominators step for the semistable specialisation of $X_H(M)$ at a place above $p \,\|\, M$: a single unit of both Gauss prolongations, fixed by the chosen inertia elements, is produced which clears the poles of the Riemann–Roch space $L(D)$ at the places where $j$ or $j(q^p)$ fails to be $A$-integral, so that the resulting basis and its $\theta$-transform have $A$-integral $q$-expansions up to constants. It is used by [`ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv`](thm.html#ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv), which constructs functions in $L(D)$ with prescribed reduction on the two components of the reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_unit_smul_riemannRochSpace_basis_coeffMap_eq_smul_forall_arithmeticGalois_smul_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

open Classical in

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_unit_smul_riemannRochSpace_basis_coeffMap_eq_smul_forall_arithmeticGalois_smul_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hFixFin : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
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
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C))

    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (hAnn : ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
    (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hS : ∀ σ ∈ S, σ ∈ A.inertiaSubgroupIn ℚ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hD : 0 ≤ D) (hgood : Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ D)
    (hDfix : ∀ V ∈ D.support, ∀ σ ∈ S, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V)
    [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace D)] :
    ∃ U : ↥(xHFunctionFieldBar M H),
      (∃ h₁ : U ∈ Rpd.R₁.integers, IsUnit (⟨U, h₁⟩ : Rpd.R₁.integers)) ∧
      (∃ h₂ : U ∈ Rpd.R₂.integers, IsUnit (⟨U, h₂⟩ : Rpd.R₂.integers)) ∧
      (∀ σ ∈ S, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • U = U) ∧
      ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) ↥((riemannRochSpace D).map (LinearMap.mulLeft (AlgebraicClosure ℚ) U))) → ↥(xHFunctionFieldBar M H),
        (∀ i, b i ∈ (riemannRochSpace D).map (LinearMap.mulLeft (AlgebraicClosure ℚ) U)) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
        (∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries ↥A), c ≠ 0 ∧
                coeffMap A.subtype y = c • ((b i : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))) ∧
             (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries ↥A), c ≠ 0 ∧
                coeffMap A.subtype y = c • ((θ (b i) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)))) ∧
        ∀ i, ∀ σ ∈ S, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • b i = b i := by sorry
