-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_isGluedPrincipal_glueData_of_forall_apply_eq_ord_of_isModel_of_coe_of_unit_of_cusp_of_orient
-- name    : ModularCurve.JHPlaceSpecialization.isGluedPrincipal_glueData_of_forall_apply_eq_ord_of_isModel_of_coe_of_unit_of_cusp_of_orient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/50c4416a-8b9f-597c-b9ab-1ff3bbbed87a
-- title:
--   Glued principality of good principal gluing data
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer with $p \mid M$ (hypothesis `hpM`) and $p^2 \nmid M$ (`hpM2`), and $H \le (\mathbb{Z}/M)^\times$ is a subgroup containing every unit of $\mathbb{Z}/M$ that reduces to $1$ in $\mathbb{Z}/(M/p)$ (`hHp`), with $M/p$ nonzero. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ (this is `A.LiesOverPrime p`), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $F_M$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the intermediate field `xHFunctionField M H` of $\overline{\mathbb{Q}}$-Laurent series, and $F_{M/p}$ for `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, where `infSubgroup p M H hpM` is the image of $H$ under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$; write $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ attached to `JHNeronObjectAtP.ΓN p M H hpM`. A place of a field extension here is a valuation subring containing the base field, distinct from the whole field and a principal ideal ring, and `Place.ord` is the associated normalised integer valuation.
--
--   The data are: an automorphism $\theta$ of $F_M$ over $\overline{\mathbb{Q}}$; two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha, \beta : F_{M/p} \to F_M$ (integrality being `hα`, `hβ`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying element is $p$ (`hpb`); a self-map $\delta$ of the set of places of $\bar F$ over $\kappa$ which, by `hδ`, acts on every place as the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM)` evaluated at the chosen lift [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$ to $\Gamma_0(M/p)$; a finite set $SS$ of pairs of places of $\bar F$ over $\kappa$ which, by `hSS`, consists exactly of the pairs in `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is of pairs $(w_1,w_2)$ with $w_2$ a supersingular place and $w_1$ the image of $w_2$ under the $q$-expansion Frobenius `qExpFrobeniusPlaceModL`; a specialisation datum `Psp : JHPlaceSpecialization p M H hpM A`, comprising a surjective map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$ together with a homomorphism on degree-zero divisor classes and the compatibilities of `sp` with $q$-expansion reduction, with divisors of functions, with inertia at $A$ and with Frobenius at $p$; and a prolongation datum `Rpd : Psp.ProlongationDatum θ`, comprising two regular prolongations $R_1, R_2$ of $A$ from $F_M$ to $\bar F$ (each a valuation subring `integers` of $F_M$ with a surjective residue map to $\bar F$ whose kernel is the maximal ideal and which induces $A \to \kappa$), such that $R_1$ is compatible with coefficientwise reduction of Laurent series over $A$ and $R_2$ is the transport of $R_1$ along $\theta$. For a place $W$ of $F_M$, `Psp.reduceFst α hα W` is $\mathrm{sp}$ of the restriction of $W$ along $\alpha$, and `Psp.reduceSnd β hβ δ W` is $\delta$ applied to $\mathrm{sp}$ of the restriction of $W$ along $\beta$; $W$ is of strict first type when $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ and $\mathrm{reduceFst}\,W$ is not $\delta$-fixed, and of strict second type when $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ and $\mathrm{reduceSnd}\,W$ is not $\delta$-fixed, where `Fixed δ v` means $\mathrm{Frob}(\delta(\mathrm{Frob}\,v)) = v$.
--
--   The hypotheses fall into the following groups. Dichotomy and finiteness: `hTD` asserts that every place of $F_M$ satisfies one of the two relations $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ or $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$; `hFix` asserts that the set of $\delta$-fixed places of $\bar F$ is finite. Model and order laws: `hmodel` is `Rpd.IsModel α β hα hβ δ`, the conjunction of the two divisor laws (for a function $f$ lying in both `integers` with nonzero residues and with divisor $D$, the pushforward along $\mathrm{reduceFst}$ of the strict-first part of $D$ reads off the order of the $R_1$-residue of $f$ at every non-$\delta$-fixed place, and symmetrically for $\mathrm{reduceSnd}$, the strict-second part and the $R_2$-residue) together with the two cusp laws `CuspLawInfty` for $\alpha$ and `CuspLawZero` for $\beta$ and $\delta$; `hO` is the order law at fixed places, which at a $\delta$-fixed affine place $v$ expresses the pushforward of the full divisor as the sum of the order of the $R_1$-residue at $v$ and the order of the $R_2$-residue at $\delta(\mathrm{Frob}\,v)$; `hRL` is the regularity law relative to $SS$ (two clauses: positivity of residue orders at $\delta$-fixed affine places, and existence of a common value at the two members of each node pair); `hNV` is the node value law relative to $SS$ (for $f$ integral on both sides with nonzero residues and a node $s \in SS$ not met by the divisor of $f$, the two residues take a common nonzero value at $s_1$ and $s_2$). Compatibilities of $\alpha$, $\beta$, $\theta$: `hα_coe` says $\alpha$ does not change the Laurent expansion, `hβ_coe` says $\beta$ replaces $q$ by $q^{p}$ (the ring map `qExpand κ p` over $\overline{\mathbb{Q}}$), `hθgal` says $\theta$ commutes with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$, and `hβθ` says $\beta$ is $\alpha$ followed by $\theta$.
--
--   Two local hypotheses `hLFst` and `hLSnd` bound residue orders at pairs of places with a common reduction. In `hLFst`: for places $Q \ne Q'$ of $F_M$, both of strict first type, with $\mathrm{reduceFst}\,Q' = \mathrm{reduceFst}\,Q$ and this common place affine (`IsAffinePlace`, i.e. it has a value at a function whose expansion is the modular $j$-$q$ series), for a natural number $n$ nonzero in $\kappa$, for $g$ in the integers of $R_1$ with nonzero $R_1$-residue such that $Q.\mathrm{ord}\,g = -n$, $Q'.\mathrm{ord}\,g = n$ and $W.\mathrm{ord}\,g = 0$ for every other strict-first place $W$ with the same $\mathrm{reduceFst}$-image, and for $e \in A$ and $\varepsilon$ in the integers of $R_1$ with nonzero $R_1$-residue such that $g = 1 + e\varepsilon$, the order of the $R_1$-residue of $\varepsilon$ at $\mathrm{reduceFst}\,Q$ is at least $-1$. The hypothesis `hLSnd` is the same statement with strict second type, $\mathrm{reduceSnd}$ and $R_2$ throughout.
--
--   The modular unit hypothesis `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ on $F_M$ with $D_1 = \operatorname{div}(u_1)$ and $D_2 = \operatorname{div}(u_2)$ such that: $u_1$ and $u_1^{-1}$ lie in the integers of $R_1$ with $R_1$-residue of $u_1$ nonzero, the pushforward along $\mathrm{reduceFst}$ of the strict-first part of $D_1$ computes the order of that residue at every non-$\delta$-fixed place, and the pushforward along $\mathrm{reduceFst}$ of the restriction of $D_1$ to the infinity-side places computes that order at $\mathrm{reduceFst}\,C$ for every infinity-side place $C$; every nonzero $f \in F_M$ admits $m \ne 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{j}$ in the integers of $R_2$ with nonzero $R_2$-residue; and symmetrically $u_2$ and $u_2^{-1}$ lie in the integers of $R_2$ with nonzero $R_2$-residue of $u_2$, the pushforward along $\mathrm{reduceSnd}$ of the strict-second part of $D_2$, respectively of the restriction of $D_2$ to the zero-side places, computes the order of that residue at non-$\delta$-fixed places, respectively at $\mathrm{reduceSnd}\,C$ for zero-side $C$; and every nonzero $f$ admits $m \ne 0$ and $j \in \mathbb{Z}$ with $f^m u_2^{j}$ in the integers of $R_1$ with nonzero $R_1$-residue. Here an infinity-side place is a cuspidal place carrying a value with residue $1$ on $x'/x^{p}$, and a zero-side place is a place cuspidal for the $p$-fold expansion carrying such a value on $x/x'^{p}$, where $x$, $x'$ have expansions the $j$-$q$ series and its $p$-fold expansion.
--
--   Cusp surjectivity and orientation: `hcusp` asserts that every non-affine place $w$ of $\bar F$ is $\mathrm{reduceFst}\,C$ for some infinity-side place $C$ and also $\mathrm{reduceSnd}\,C$ for some zero-side place $C$; `horientInf` asserts $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,C)) = \mathrm{reduceSnd}\,C$ for infinity-side $C$, and `horient0` asserts $\mathrm{reduceFst}\,C = \mathrm{Frob}(\mathrm{reduceSnd}\,C)$ for zero-side $C$. Finally `hSSne` asserts that $SS$ is nonempty.
--
--   The divisor in question: $f \in F_M$ is nonzero, $D$ is the divisor with $D(V) = V.\mathrm{ord}\,f$ for every place $V$ (`hDf`), $D$ is good (`hgood`: every place in the support of $D$ is of strict first or of strict second type), and the gluing datum $\mathrm{glueData} = \bigl(\mathrm{reduceFst}_*(\text{strict-first part of } D),\ \mathrm{reduceSnd}_*(\text{strict-second part of } D),\ 0\bigr)$ is admissible (`hadm`: both divisor components have degree zero and, for every $s \in SS$, the first component vanishes at $s_1$ and the second at $s_2$).
--
--   The conclusion is that this gluing datum is glued-principal: there exist $g_1, g_2 \in \bar F$ and maps $a, b : SS \to \kappa^{\times}$ such that $g_1 \ne 0$; $g_2 \ne 0$; for every place $v$ of $\bar F$ over $\kappa$ the first component $\mathrm{reduceFst}_*(\text{strict-first part of } D)$ evaluated at $v$ equals $v.\mathrm{ord}\,g_1$; for every such $v$ the second component $\mathrm{reduceSnd}_*(\text{strict-second part of } D)$ evaluated at $v$ equals $v.\mathrm{ord}\,g_2$; for every $s \in SS$ the place $s_1$ has value $a(s)$ at $g_1$ and the place $s_2$ has value $b(s)$ at $g_2$ (that is, $g_1$ lies in the valuation ring of $s_1$ with residue the image of $a(s)$, and likewise for $g_2$ at $s_2$); and the third component of the gluing datum, which is $0$, is the function $s \mapsto \mathrm{ofMul}(a(s)/b(s))$, so that $a(s) = b(s)$ for all $s \in SS$.
--
--   This is the glued-principality step for $X_H(M)$: a principal divisor on the geometric function field of $X_H(M)$ which is good for the $\delta$-corrected reductions and whose gluing datum is admissible has that gluing datum represented by a pair of functions on the two components of the reduction, agreeing at the supersingular nodes. It is the input used to show that the glued specialisation homomorphism on degree-zero divisor classes is well defined on good representatives, via [`ModularCurve.JHPlaceSpecialization.exists_addMonoidHom_isGluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_orient`](thm.html#ModularCurve.JHPlaceSpecialization.exists_addMonoidHom_isGluedSpecialization_of_isModel_of_coe_of_unit_of_cusp_of_orient); the proof combines the existence of a suitable multiple with nonzero residues on both sides with the variant of the present statement in which that integrality is assumed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_isGluedPrincipal_glueData_of_forall_apply_eq_ord_of_isModel_of_coe_of_unit_of_cusp_of_orient.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

open Classical in

theorem ModularCurve.JHPlaceSpecialization.isGluedPrincipal_glueData_of_forall_apply_eq_ord_of_isModel_of_coe_of_unit_of_cusp_of_orient
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hFix : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α β hα hβ δ Q → Psp.IsStrictFst α β hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α β hα hβ δ Q → Psp.IsStrictSnd α β hα hβ δ Q' →
      Psp.reduceSnd β hβ δ Q' = Psp.reduceSnd β hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd β hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α β hα hβ δ W → Psp.reduceSnd β hβ δ W = Psp.reduceSnd β hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd β hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd β hβ δ C) =
            (Psp.reduceSnd β hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd β hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd β hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd β hβ δ C))
    (hSSne : SS.Nonempty)
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hDf : ∀ V, D V = V.ord f)
    (hgood : Psp.IsGoodDiv α β hα hβ δ D)
    (hadm : Psp.glueData α β hα hβ δ SS D ∈ GluingData.admissible SS) :
    GluingData.IsGluedPrincipal SS (Psp.glueData α β hα hβ δ SS D) := by sorry
