-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_inertiaFixed_isStrict_gluedMk_glueData_eq_of_annulus
-- name    : ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isStrict_gluedMk_glueData_eq_of_annulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/9ce43391-aaf2-5e99-935f-ccbdabd76b64
-- title:
--   Glued Picard classes from inertia-fixed strict divisors on X_H(M)
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer with $p \mid M$ (hypothesis `hpM`) and $p^2 \nmid M$ (hypothesis `hpM2`), and $H \le (\mathbf{Z}/M)^\times$ is a subgroup containing every unit whose image under the reduction $(\mathbf{Z}/M)^\times \to (\mathbf{Z}/(M/p))^\times$ is trivial (hypothesis `hHp`). Write $F_M$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbf{Q}}$ of the $q$-expansion function field of $X_H(M)$, and $F_{M/p}$ for `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, the corresponding field at level $M/p$ for the image `infSubgroup p M H hpM` of $H$ under that reduction map. Further, $A$ is a valuation subring of $\overline{\mathbf{Q}}$ lying over $p$ in the sense that $p$ is a non-unit of $A$ (hypothesis `hA`), with residue field $\kappa =$ `ResidueField ↥A` assumed of characteristic $p$ and algebraically closed; $F_b$ denotes `Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ for the group `ΓN p M H hpM`, and $\Phi$ denotes the Frobenius operator `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` on places of $F_b$, given by restriction along the $q$-expansion Frobenius.
--
--   The remaining data are: an automorphism $\theta$ of $F_M$ over $\overline{\mathbf{Q}}$; an algebra homomorphism $\alpha : F_{M/p} \to F_M$, integral (`hα`), such that $\theta \circ \alpha$ is integral as well (`hβ`) — below $\beta$ abbreviates `θ.toAlgHom.comp α`, that is $\alpha$ followed by $\theta$; the normalisations `hα_coe`, that $\alpha$ is the identity on underlying Laurent series, and `hβ_coe`, that $\beta$ acts on underlying Laurent series by $q \mapsto q^p$ (`qExpand (AlgebraicClosure ℚ) p`); a unit $pb$ of $\mathbf{Z}/(M/p)$ whose underlying element is $p$ (`hpb`); a self-map $\delta$ of the places of $F_b$ which by `hδ` is the semilinear action of the diamond automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)`; a finite set $SS$ of pairs of places of $F_b$ which by `hSS` consists exactly of the pairs $(\Phi v, v)$ with $v$ a supersingular place in `ssPlacesQExp κ (ΓN p M H hpM) p`; a place-specialisation kit `Psp : JHPlaceSpecialization p M H hpM A`, with reductions `Psp.reduceFst α hα W = Psp.sp (W.restrictAlong α hα)` and `Psp.reduceSnd β hβ δ W = δ (Psp.sp (W.restrictAlong β hβ))`; and a prolongation datum `Rpd` for `Psp` and $\theta$, with its two regular prolongations `Rpd.R₁`, `Rpd.R₂` and their residue maps. Recall that a place $v$ of $F_b$ is `Fixed` for $\delta$ when $\Phi(\delta(\Phi v)) = v$, that a place $W$ of $F_M$ is `IsStrictFst` when $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not `Fixed`, and `IsStrictSnd` when $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not `Fixed`, where $\mathrm{red}_1, \mathrm{red}_2$ are the two reductions just described; and that $v$ is an `IsAffinePlace` when some element of $F_b$ with Laurent series `jqModC κ` has a value at $v$.
--
--   The hypotheses fall into the following groups.
--
--   Fixedness and structural laws. `hFix`: every supersingular place $y$ of $F_b$ and its Frobenius image $\Phi y$ are `Fixed` for $\delta$. `hTD` (`TypeDichotomy`): for every place $W$ of $F_M$, either $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ or $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$. `hmodel` (`IsModel`): the conjunction of the two divisor laws and the two cusp laws of `Rpd` for $\alpha, \beta, \delta$. `hO` (`OrderLawFixed`): for $f \in F_M$ integral for both prolongations with nonzero residues, and $D$ the divisor of $f$, the push-forward $\mathrm{red}_1{}_* D$ at a `Fixed` affine place $v$ equals $\operatorname{ord}_v$ of the first residue of $f$ plus $\operatorname{ord}_{\delta(\Phi v)}$ of the second residue. `hreg` (`RegularityLaw` for $SS$, two clauses): positivity of the residues' orders at `Fixed` affine places, and existence of a common value of the two residues at the two members of each pair in $SS$, whenever $f$ has no poles above the relevant place. `hnv` (`NodeValueLaw` for $SS$): for such $f$ and $s \in SS$, if no place $V$ with $\operatorname{ord}_V f \ne 0$ reduces to $(s_1, s_2)$ under $(\mathrm{red}_1, \mathrm{red}_2)$, then the two residues take one and the same nonzero value $c \in \kappa$ at $s_1$ and at $s_2$. `hθgal`: $\theta$ commutes with the arithmetic Galois action `arithmeticGalois (xHFunctionField M H) σ` of every $\sigma \in \operatorname{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$. `hFixFin`: the set of $\delta$-fixed places of $F_b$ is finite.
--
--   Local laws at affine places (`hLFst`, `hLSnd`, symmetric to each other). On the first side: for all strict-first places $Q \ne Q'$ of $F_M$ with the same first reduction, that reduction being an affine place, for every natural number $n$ nonzero in $\kappa$, every $g$ in `Rpd.R₁.integers` with nonzero first residue such that $\operatorname{ord}_Q g = -n$, $\operatorname{ord}_{Q'} g = n$ and $\operatorname{ord}_W g = 0$ for every further strict-first place $W$ with the same first reduction, and every $e \in A$ and $\varepsilon$ in `Rpd.R₁.integers` with nonzero first residue such that $g = 1 + e\varepsilon$, one has $-1 \le \operatorname{ord}_{\mathrm{red}_1 Q}$ of the first residue of $\varepsilon$. The hypothesis `hLSnd` is the same statement with `IsStrictSnd`, $\mathrm{red}_2$ and `Rpd.R₂` in place of `IsStrictFst`, $\mathrm{red}_1$ and `Rpd.R₁`.
--
--   Units on the two sides (`hUnit`). There exist $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ on $F_M$ with $D_i(W) = \operatorname{ord}_W u_i$ for all $W$, such that: $u_1$ and $u_1^{-1}$ lie in `Rpd.R₁.integers`, the first residue of $u_1$ is nonzero, at every place $v$ of $F_b$ that is not `Fixed` the value of $\mathrm{red}_1{}_*(\mathrm{fstDiv}\, D_1)$ is $\operatorname{ord}_v$ of that residue, and for every `IsInftySide` place $C$ the value at $\mathrm{red}_1 C$ of $\mathrm{red}_1{}_*$ of the part of $D_1$ supported on `IsInftySide` places equals $\operatorname{ord}_{\mathrm{red}_1 C}$ of that residue; every nonzero $f \in F_M$ admits $m \ne 0$ in $\mathbf{N}$ and $j \in \mathbf{Z}$ with $f^m u_1^{\,j}$ in `Rpd.R₂.integers` of nonzero second residue; and symmetrically $u_2$, $u_2^{-1}$ lie in `Rpd.R₂.integers` with nonzero second residue, the analogous two identities hold for $\mathrm{red}_2{}_*(\mathrm{sndDiv}\, D_2)$ at non-`Fixed` places and for `IsZeroSide` places, and every nonzero $f$ admits $m \ne 0$ and $j$ with $f^m u_2^{\,j}$ in `Rpd.R₁.integers` of nonzero first residue.
--
--   Cusps and orientation. `hcusp`: every place $w$ of $F_b$ that is not an affine place is the first reduction of some `IsInftySide` place and the second reduction of some `IsZeroSide` place. `horientInf`: for every `IsInftySide` place $C$, $\delta(\Phi(\mathrm{red}_1 C)) = \mathrm{red}_2 C$. `horient0`: for every `IsZeroSide` place $C$, $\mathrm{red}_1 C = \Phi(\mathrm{red}_2 C)$.
--
--   Annuli (`e`, `he`, `hAnn`). A function $e$ on $SS$ with $e(s) > 0$, and for each $s \in SS$ an annulus `An : Annulus A F_M` over $A$ such that: the domain of `An` consists exactly of the places $W$ with $\mathrm{red}_1 W = s_1$ that are neither strict-first nor strict-second; the modulus of `An` is $p^{e(s)}$ times a unit of $A$; the parameter of `An` is fixed by `arithmeticGalois (xHFunctionField M H) σ` for every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`; the product of the inverse modulus with the parameter lies in `Rpd.R₁.integers`; the parameter lies in `Rpd.R₂.integers` with nonzero second residue, its second residue has order $1$ at $s_2$, and for every $f$ in `Rpd.R₂.integers` with nonzero second residue and no zeros or poles on the annulus, the value of $f$ at each $P$ in the domain, multiplied by the value of the parameter raised to minus the order at $s_2$ of the second residue of $f$, lies in $A$ and is a unit there; and symmetrically the modulus times the inverse parameter lies in `Rpd.R₁.integers`, its first residue has order $1$ at $s_1$, and the same unit-normalisation property holds on the first side.
--
--   Finally, $g$ is an arbitrary element of the glued degree-zero class group `GluedPic0 κ F_b SS`, the quotient of the admissible gluing data by the glued principal ones.
--
--   The conclusion asserts the existence of a divisor $D_t$ of degree zero on $F_M$ over $\overline{\mathbf{Q}}$ such that:
--
--   (i) every place $V$ in the support of $D_t$ is fixed by the arithmetic Galois action of every $\sigma \in$ `A.inertiaSubgroupIn ℚ`, and is either `IsStrictFst` or `IsStrictSnd` for $\alpha, \beta, \delta$;
--
--   (ii) the gluing datum `Psp.glueData α β hα hβ δ SS D_t`, namely the pair of push-forwards $\mathrm{red}_1{}_*(\mathrm{fstDiv}\, D_t)$ and $\mathrm{red}_2{}_*(\mathrm{sndDiv}\, D_t)$ together with the trivial node-unit component, is admissible for $SS$ — both divisors have degree zero and vanish at $s_1$, resp. $s_2$, for each $s \in SS$ — and its class `GluedPic0.mk SS` in `GluedPic0 κ F_b SS` is equal to $g$.
--
--   This is the surjectivity, or torus-lift, step for the glued degree-zero class group attached to the special fibre at $p$ of $X_H(M)$ when $p$ exactly divides $M$: every glued class is realised by a degree-zero divisor on the generic fibre whose support consists of inertia-fixed places of strict type. It feeds the refinement [`ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isStrict_add_isGoodDiv_gluedMk_eq_zero_add_principal_of_isTwistType_of_inertiaStable_of_annulus_of_fixRead`](thm.html#ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isStrict_add_isGoodDiv_gluedMk_eq_zero_add_principal_of_isTwistType_of_inertiaStable_of_annulus_of_fixRead), in the analysis of the semistable reduction of the Jacobian of $X_H(M)$ at $p$ and of its component and character groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_inertiaFixed_isStrict_gluedMk_glueData_eq_of_annulus.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

open Classical in

theorem ModularCurve.JHPlaceSpecialization.exists_inertiaFixed_isStrict_gluedMk_glueData_eq_of_annulus
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
    (g : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS) :
    ∃ Dt : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (∀ V ∈ (Dt : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧
        (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V)) ∧
      ∃ hadm : Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (Dt : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS,
        GluedPic0.mk SS ⟨Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (Dt : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm⟩ = g := by sorry
