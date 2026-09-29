-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_componentMap_gluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg
-- name    : ModularCurve.JHPlaceSpecialization.exists_componentMap_gluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/57166db0-d8db-5c95-ade6-75e2f741f513
-- title:
--   Component map and glued specialization for X_H(M) at p ∥ M
-- statement:
--   Throughout, $p$ is a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and $H \le (\mathbb{Z}/M)^\times$ is a subgroup containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$ (hypotheses `hpM`, `hpM2`, `hHp`, together with $M/p \neq 0$). Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with `A.LiesOverPrime p`, i.e. $p$ is a non-unit of $A$, whose residue field $\kappa =$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed. Write $F_M$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of $X_H(M)$ inside $\overline{\mathbb{Q}}((q))$, $F_{M/p}$ for the corresponding field at level $M/p$ with the subgroup `infSubgroup p M H hpM` (the image of $H$ in $(\mathbb{Z}/(M/p))^\times$), and $\bar F =$ `Fbar p M H hpM κ` for the characteristic-$p$ $q$-expansion function field attached to `ΓN p M H hpM` over $\kappa$. Let $\varphi$ denote the Frobenius operation `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` on places of $\bar F$.
--
--   The degeneracy data consist of an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$ and an $\overline{\mathbb{Q}}$-algebra homomorphism $\alpha : F_{M/p} \to F_M$, with $\beta := \theta \circ \alpha$, both integral (`hα`, `hβ`), normalised on $q$-expansions by `hα_coe` ($\alpha$ is the identity on Laurent series) and `hβ_coe` ($\beta$ acts by `qExpand` $p$, that is $q \mapsto q^p$); `hθgal` requires $\theta$ to commute with the arithmetic Galois action `arithmeticGalois` of $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ on $F_M$. A unit $pb$ of $\mathbb{Z}/(M/p)$ reducing to $p$ (`hpb`) provides the diamond operator, and $\delta$ is an operation on places of $\bar F$ which, by `hδ`, is the action of the semilinear automorphism attached by `diamondActionModL` to a $\Gamma_0(M/p)$-lift of $pb$. The finite set $SS$ of pairs of places of $\bar F$ is required by `hSS` to be exactly `ssNodePairsQExp κ (ΓN p M H hpM) p`, i.e. the pairs $s$ with $s.2$ supersingular and $s.1 = \varphi(s.2)$.
--
--   The reduction data consist of `Psp : JHPlaceSpecialization p M H hpM A` — a surjective specialization $\mathrm{sp}$ of places of $F_{M/p}$ to places of $\bar F$, together with a map on degree-zero divisor classes and the compatibilities with $q$-expansions, with divisors, and with inertia and Frobenius elements recorded in that structure — and `Rpd : Psp.ProlongationDatum θ`, a pair of regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue maps to $\bar F$, matched through $\theta$. For a place $W$ of $F_M$, `Psp.reduceFst α hα W` is $\mathrm{sp}$ of the restriction of $W$ along $\alpha$, and `Psp.reduceSnd β hβ δ W` is $\delta$ applied to $\mathrm{sp}$ of the restriction along $\beta$; $W$ is strict-first when $\delta(\varphi(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ and $\mathrm{reduceFst}\,W$ is not `Fixed` for $\delta$ (a place $v$ being `Fixed` means $\varphi(\delta(\varphi\,v)) = v$), and strict-second when $\mathrm{reduceFst}\,W = \varphi(\mathrm{reduceSnd}\,W)$ and $\mathrm{reduceSnd}\,W$ is not `Fixed`; a divisor is good (`IsGoodDiv`) when every place of its support is strict-first or strict-second, and `fstDiv`, `sndDiv` are the restrictions of a divisor to its strict-first, respectively strict-second, places. A place $v$ of $\bar F$ is affine (`IsAffinePlace`) when some element of $\bar F$ with $q$-expansion `jqModC κ` has a value at $v$.
--
--   The law block consists of: `hFix`, requiring every supersingular place $y \in$ `ssPlacesQExp κ (ΓN p M H hpM) p` and its Frobenius image $\varphi(y)$ to be `Fixed` for $\delta$; `hTD`, the type dichotomy, that every place $W$ of $F_M$ satisfies $\mathrm{reduceFst}\,W = \varphi(\mathrm{reduceSnd}\,W)$ or $\delta(\varphi(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$; `hmodel`, that `Rpd` is a model, i.e. the two divisor laws and the two cusp laws of `IsModel` hold for $\alpha, \beta, \delta$; `hO`, the order law `OrderLawFixed` at `Fixed` affine places, expressing the pushforward of a divisor along `reduceFst` there as the sum of the orders of the two residues; `hreg`, the regularity law `RegularityLaw` for $SS$ (regularity of residues at `Fixed` affine places, and common values at the two coordinates of each $s \in SS$); and `hnv`, the node-value law `NodeValueLaw` for $SS$ (for a function integral with nonzero residue on both sides and whose divisor avoids a node, the two residues take a common nonzero value at $s.1$ and $s.2$). In addition `hFixFin` requires the set of $\delta$-`Fixed` places of $\bar F$ to be finite.
--
--   Two further one-sided hypotheses `hLFst` and `hLSnd` govern pole–zero pairs. `hLFst` requires: whenever $Q \neq Q'$ are strict-first places with the same image $v = \mathrm{reduceFst}\,Q$, this $v$ being affine, $n$ a natural number nonzero in $\kappa$, and $g$ is $R_1$-integral with nonzero residue, with $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict-first place $W$ above $v$, and $g = 1 + e\,\varepsilon$ with $e \in A$ and $\varepsilon$ $R_1$-integral with nonzero residue, then $-1 \le \mathrm{ord}_v$ of the $R_1$-residue of $\varepsilon$. `hLSnd` is the mirror statement for strict-second places, `reduceSnd` and $R_2$.
--
--   The hypothesis `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ with $D_i(W) = \mathrm{ord}_W u_i$, such that: $u_1$ and $u_1^{-1}$ are $R_1$-integral with nonzero residue of $u_1$, the pushforward along `reduceFst` of `fstDiv` $D_1$ agrees at every non-`Fixed` place $v$ with $\mathrm{ord}_v$ of the residue of $u_1$, and the pushforward along `reduceFst` of the part of $D_1$ supported on the infinity-side places (`IsInftySide`) agrees at $\mathrm{reduceFst}\,C$, for every infinity-side place $C$, with $\mathrm{ord}$ of that residue there; moreover every nonzero $f \in F_M$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j}$ $R_2$-integral of nonzero residue. The conditions on $u_2$ mirror these with $R_2$, `sndDiv`, `reduceSnd`, the zero-side places (`IsZeroSide`), and $f^m u_2^{\,j}$ $R_1$-integral of nonzero residue. Here `IsInftySide` and `IsZeroSide` are the cuspidal conditions of the two sides, involving a value of $x'/x^p$, respectively $x/x'^p$, congruent to $1$, for $x, x'$ with $q$-expansions `jqModC` and `qExpand p jqModC`.
--
--   The hypothesis `hcusp` requires every non-affine place $w$ of $\bar F$ to be the `reduceFst`-image of some infinity-side place and the `reduceSnd`-image of some zero-side place. The orientation hypotheses require $\delta(\varphi(\mathrm{reduceFst}\,C)) = \mathrm{reduceSnd}\,C$ for every infinity-side $C$ (`horientInf`) and $\mathrm{reduceFst}\,C = \varphi(\mathrm{reduceSnd}\,C)$ for every zero-side $C$ (`horient0`).
--
--   The widths are given: $e : SS \to \mathbb{N}$ with $e(s) > 0$ for all $s$ (`he`). The hypothesis `hAnn` requires, for each $s \in SS$, an annulus $An$ of [`AlgebraicCurve.Annulus A F_M`](def/AlgebraicCurve_SemistableCharts.html#L86) — a set of rational places, a parameter and a modulus in the maximal ideal of $A$, subject to the axioms of that structure — with the six properties (summarised here): its domain consists exactly of the places $W$ with $\mathrm{reduceFst}\,W = s.1$ which are neither strict-first nor strict-second; its modulus is $p^{e(s)}$ times a unit of $A$; its parameter is fixed by `arithmeticGalois` of every element of `A.inertiaSubgroupIn ℚ`; the product of the inverse modulus with the parameter is $R_1$-integral; the parameter is $R_2$-integral with nonzero residue; and, on the two sides, the parameter (respectively the modulus times the inverse parameter) has residue of order $1$ at $s.2$ (respectively $s.1$) and computes the evaluation of any integral function with nonzero residue and zero order on the annulus up to units of $A$.
--
--   The slope hypothesis `hVSlope` requires: for every family $An$ of annuli indexed by $SS$ satisfying, for each $s$, the same list of properties as in `hAnn`, and for every natural number $k$ divisible by all the $e(s)$, there exist $f \in F_M$ nonzero and $c \in \overline{\mathbb{Q}}$ with $c \cdot f$ $R_1$-integral of nonzero residue, such that every divisor equal to the divisor of $f$ is good, $\mathrm{ord}_V f = 0$ for every place $V$ whose `reduceFst`-image is `Fixed` and distinct from all $s.1$, $\mathrm{ord}_v$ of the residue of $c \cdot f$ vanishes at every `Fixed` place $v$ distinct from all $s.1$, and for each $s$ there is $a \neq 0$ in $\overline{\mathbb{Q}}$ with $\mathrm{ord}_P f = 0$ and with the evaluation of $f$ at $P$, times $a$, times the $(-k/e(s))$-th power of the evaluation of the parameter, a unit of $A$, for every $P$ in the domain of $An(s)$.
--
--   Finally, the reading hypotheses `hFixReadFst` and `hFixReadSnd` require that for an $R_1$-integral (respectively $R_2$-integral) $g$ with nonzero residue and a `Fixed` place $v$ distinct from all $s.1$ (respectively all $s.2$), vanishing of $\mathrm{ord}_V g$ at all places $V$ above $v$ for `reduceFst` (respectively `reduceSnd`) forces $\mathrm{ord}_v$ of the residue of $g$ to vanish; and the regularity hypotheses `hFixRegFst`, `hFixRegSnd` require, for such $v$ in addition affine, that $0 \le \mathrm{ord}_V g$ at all places above $v$ forces $0 \le \mathrm{ord}_v$ of the residue of $g$.
--
--   Under all these hypotheses, the conclusion asserts the existence of two additive group homomorphisms from `JHPlaceSpecialization.inertiaInvariants M H A`, the subgroup of the classes in $J_H(M) =$ `Pic0 (AlgebraicClosure ℚ) F_M` fixed by every element of `A.inertiaSubgroupIn ℚ`: a homomorphism `comp` to `componentGroup e`, the quotient of `Module.Dual ℤ (characterLattice ↥SS)` by the range of `gramMap e`, and a homomorphism `spJ` to `GluedPic0 κ F̄ SS`, the quotient of the admissible gluing data by the glued principal ones, such that
--
--   (i) `comp` is surjective;
--
--   (ii) for every $x$ in the inertia invariants, `comp x = 0` holds if and only if $x$, viewed in `JH M H`, is a good class in the sense of `IsGoodClass`: there is a degree-zero divisor $D$ on $F_M$ which is good, whose gluing datum `glueData` for $SS$ is admissible, and whose class is $x$;
--
--   (iii) `spJ` is a glued specialization in the sense of `IsGluedSpecialization`: for every degree-zero divisor $D$ on $F_M$ whose class lies in the inertia invariants and every admissible gluing datum $x$ equal to the `glueData` of $D$, if $D$ is good then `spJ` sends the class of $D$ to the class of $x$ in `GluedPic0 κ F̄ SS`.
--
--   This is the component-group and glued-specialization step for the Jacobian of $X_H(M)$ at a prime $p$ exactly dividing the level, in the Deligne–Rapoport picture of the special fibre as two copies of the level-$M/p$ curve glued at the supersingular points, with the component group computed by the Raynaud-type width pairing attached to the widths $e$. It is used by [`ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen), which assembles the model data at $p$ feeding into level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_componentMap_gluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

open Classical in

theorem ModularCurve.JHPlaceSpecialization.exists_componentMap_gluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_attachedAnnulus_of_slope_of_fixReg
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

    (hVSlope : ∀ An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
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
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))) →
      ∀ k : ℕ, (∀ s : ↥SS, e s ∣ k) →
        ∃ (f : ↥(xHFunctionFieldBar M H)) (c : AlgebraicClosure ℚ) (hc : c • f ∈ Rpd.R₁.integers),
          f ≠ 0 ∧ Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
          (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) → Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G) ∧
          (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) →
            (∀ s ∈ SS, Psp.reduceFst α hα V ≠ s.1) → V.ord f = 0) ∧
          (∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
            v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0) ∧
          (∀ s : ↥SS, ∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord f = 0 ∧
            ∃ h : P.evalAt f * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hFixReadFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → V.ord g = 0) →
        v.ord (Rpd.R₁.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0)
    (hFixReadSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → V.ord g = 0) →
        v.ord (Rpd.R₂.residue ⟨g, hg⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0)

    (hFixRegFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.1) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₁.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hFixRegSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (hg : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg⟩ ≠ 0 →
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → (∀ s ∈ SS, v ≠ s.2) →
        (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = v → 0 ≤ V.ord g) →
        0 ≤ v.ord (Rpd.R₂.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) :
    ∃ (comp : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ componentGroup e)
      (spJ : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS),
      Function.Surjective comp ∧
      (∀ x : ↥(JHPlaceSpecialization.inertiaInvariants M H A),
        comp x = 0 ↔ Psp.IsGoodClass α (θ.toAlgHom.comp α) hα hβ δ SS (x : JH M H)) ∧
      Psp.IsGluedSpecialization α (θ.toAlgHom.comp α) hα hβ δ SS spJ := by sorry
