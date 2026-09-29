-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_gluedMk_eq_zero_pic0Mk_eq_of_isTwistOf_of_gluedMk_twistSpData_eq_zero_of_inertiaStable_of_annulus
-- name    : ModularCurve.JHPlaceSpecialization.exists_isGoodDiv_gluedMk_eq_zero_pic0Mk_eq_of_isTwistOf_of_gluedMk_twistSpData_eq_zero_of_inertiaStable_of_annulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/2aab719c-5923-5d66-b426-e8db7b4c9072
-- title:
--   Good representative with vanishing glued class for a twisted divisor
-- statement:
--   Throughout, $p$ is a prime and $M$ a non-zero natural number with $p \mid M$ and $p^2 \nmid M$, $H$ is a subgroup of $(\mathbb{Z}/M)^{\times}$ containing (hypothesis `hHp`) every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^{\times}$, and $M/p$ is non-zero. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA`, i.e. `A.LiesOverPrime p`) whose residue field $\kappa :=$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. Write $F_M :=$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of $\Gamma_H(M)$, $F_{M/p} :=$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for its analogue at level $M/p$ with the image subgroup, and $\bar F :=$ `Fbar p M H hpM κ` for the $q$-expansion function field of `ΓN p M H hpM` over $\kappa$.
--
--   The maps are: $\theta$, an automorphism of $F_M$ over $\overline{\mathbb{Q}}$, commuting with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$ (`hθgal`); and $\alpha : F_{M/p} \to F_M$, an $\overline{\mathbb{Q}}$-algebra map which is integral (`hα`) and is the identity on underlying Laurent series (`hα_coe`). The second degeneracy map is $\beta := \theta \circ \alpha$, also integral (`hβ`), and on Laurent series it is the substitution $q \mapsto q^{p}$, i.e. `qExpand (AlgebraicClosure ℚ) p` (`hβ_coe`). Moreover $pb$ is a unit of $\mathbb{Z}/(M/p)$ whose underlying class is $p$ (`hpb`), and $\delta$ is a self-map of the set of places of $\bar F$ over $\kappa$ which (`hδ`) is the action, through `SemilinearAut.ofAlgAut`, of the diamond automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM)` evaluated at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36). Finally $SS$ is a finite set of pairs of places of $\bar F$ which (`hSS`) is exactly `ssNodePairsQExp κ (ΓN p M H hpM) p`: the pairs $s$ with $s.2$ a supersingular place and $s.1$ its $q$-expansion Frobenius image.
--
--   The specialisation data are `Psp : JHPlaceSpecialization p M H hpM A` (a specialisation $\mathrm{sp}$ of places of $F_{M/p}$ to places of $\bar F$ together with a map on degree-zero divisor classes and the compatibilities recorded in that structure) and a prolongation datum `Rpd : Psp.ProlongationDatum θ`, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with values in $\bar F$, tied to one another by $\theta$. For a place $W$ of $F_M$ one writes $\mathrm{red}_1 W :=$ `Psp.reduceFst α hα W` $= \mathrm{sp}(W|_{\alpha})$ and $\mathrm{red}_2 W :=$ `Psp.reduceSnd β hβ δ W` $= \delta(\mathrm{sp}(W|_{\beta}))$; a place $v$ of $\bar F$ is $\delta$-fixed when $\mathrm{Frob}(\delta(\mathrm{Frob}\, v)) = v$, and $W$ is strict of the first (second) kind when $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not $\delta$-fixed (respectively $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not $\delta$-fixed).
--
--   The hypotheses fall into the following groups, whose content is summarised here.
--
--   (i) Combinatorics of the special fibre: `hFix` states that every supersingular place in `ssPlacesQExp κ (ΓN p M H hpM) p` and its Frobenius image are $\delta$-fixed; `hTD` is the type dichotomy, that every place $W$ of $F_M$ satisfies $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hFixFin` states that the set of $\delta$-fixed places of $\bar F$ is finite; `hcusp` states that every non-affine place of $\bar F$ is both $\mathrm{red}_1$ of some place of $F_M$ lying on the $\infty$-side and $\mathrm{red}_2$ of some place on the $0$-side; `horientInf` and `horient0` orient the two cuspidal sides, requiring $\delta(\mathrm{Frob}(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for $C$ on the $\infty$-side and $\mathrm{red}_1 C = \mathrm{Frob}(\mathrm{red}_2 C)$ for $C$ on the $0$-side.
--
--   (ii) The laws of the model: `hmodel` is `Rpd.IsModel`, the conjunction of the two divisor laws (the $\mathrm{red}_1$-pushforward of the strict-first part of a principal divisor reads off the order of the $R_1$-residue at non-$\delta$-fixed places, and symmetrically for $\mathrm{red}_2$, $R_2$) and the two cusp laws at the $\infty$- and $0$-sides; `hO` is the order law at $\delta$-fixed affine places; `hreg` is the two-clause regularity law relative to $SS$; `hnv` is the node-value law relative to $SS$.
--
--   (iii) One-sided local laws `hLFst` and `hLSnd`: for two distinct places $Q \neq Q'$ strict of the first (respectively second) kind with equal and affine reduction, for $n$ a natural number non-zero in $\kappa$, for $g$ in the integers of $R_1$ (respectively $R_2$) with non-zero residue such that $Q.\mathrm{ord}\,g = -n$, $Q'.\mathrm{ord}\,g = n$ and $W.\mathrm{ord}\,g = 0$ for every further strict place $W$ with the same reduction, and for $b \in A$ and $\varepsilon$ in the same ring of integers with non-zero residue such that $g = 1 + b\,\varepsilon$, the order of the residue of $\varepsilon$ at the common reduction of $Q$ is at least $-1$.
--
--   (iv) Unit normalisations `hUnit`: there are $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ equal to the divisors of $u_1$ and $u_2$ place by place, such that $u_1$ and $u_1^{-1}$ lie in the integers of $R_1$ with non-zero residue, the $\mathrm{red}_1$-pushforward of the strict-first part of $D_1$ reads off the orders of the $R_1$-residue of $u_1$ at all non-$\delta$-fixed places and the $\infty$-side part of $D_1$ does so at the reductions of $\infty$-side places, and every non-zero $f$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^{m}u_1^{j}$ in the integers of $R_2$ with non-zero residue; together with the mirror-image clauses for $u_2$, $R_2$, the $0$-side and $R_1$.
--
--   (v) Annuli at the nodes: $e : SS \to \mathbb{N}$ is positive (`he`), and `hAnn` asserts, for each $s \in SS$, the existence of an annulus `An : Annulus A F_M` whose domain consists exactly of the places $W$ with $\mathrm{red}_1 W = s.1$ that are strict of neither kind, whose modulus is $p^{e(s)}$ times a unit of $A$, whose parameter is invariant under the arithmetic Galois action of the inertia subgroup `A.inertiaSubgroupIn ℚ`, with $\mathrm{modulus}^{-1}\cdot \mathrm{param}$ in the integers of $R_1$ and $\mathrm{param}$ in the integers of $R_2$ with non-zero residue, and which satisfies two dual normalisation clauses: the $R_2$-residue of the parameter has order $1$ at $s.2$ and, for $f$ in the integers of $R_2$ with non-zero residue and vanishing order on the annulus domain, the quantity $P(f)\cdot P(\mathrm{param})^{-\mathrm{ord}_{s.2}(\text{residue of } f)}$ is a unit of $A$ at every $P$ in the domain; and the same with the flipped parameter $\mathrm{modulus}\cdot\mathrm{param}^{-1}$, $R_1$ and $s.1$. A family $An$ of such annuli is fixed, together with the proof `hAn` of exactly these clauses for it.
--
--   (vi) The vertical slope hypothesis `hVSlope`: for every family of annuli satisfying the clauses of (v) and every $k$ divisible by all $e(s)$, there exist $f \neq 0$ in $F_M$ and $c \in \overline{\mathbb{Q}}$ with $c \cdot f$ in the integers of $R_1$ with non-zero residue, such that the divisor of $f$ is good (its support consists of strict places), $f$ has order $0$ at every place whose $\mathrm{red}_1$ is $\delta$-fixed and is not a first node coordinate, the $R_1$-residue of $c\cdot f$ has order $0$ at every $\delta$-fixed place that is no first node coordinate, and for each $s$ there is $a \neq 0$ in $\overline{\mathbb{Q}}$ with $P.\mathrm{ord}\,f = 0$ and $P(f)\,a\,P(\mathrm{param})^{-(k/e(s))}$ a unit of $A$ for all $P$ in the domain of the $s$-th annulus.
--
--   (vii) Fixed-place readings and regularity: `hFixReadFst` and `hFixReadSnd` state that a function in the integers of $R_1$ (respectively $R_2$) with non-zero residue, having order $0$ at all places above a $\delta$-fixed place $v$ which is not a first (respectively second) node coordinate, has residue of order $0$ at $v$; `hFixRegFst` and `hFixRegSnd` are the corresponding statements with $\ge 0$ in place of $= 0$, for $v$ in addition affine.
--
--   (viii) Positions: $\mathrm{pos} : SS \to \mathrm{Places}(F_M) \to \mathbb{Q}$ satisfies the annulus position law `hpos` (on the domain of the $s$-th annulus, $0 < \mathrm{pos}\,s\,V < e(s)$ together with the valuation-slope identity of `AnnulusPositionLaw`), is invariant under the inertia action (`hposσ`), and (`hposD`) for every $s$ and every integer $d$ with $0 < d < e(s)$ there is an inertia-fixed place in the $s$-th annulus domain with $\mathrm{pos}\,s\,V = d$.
--
--   (ix) The twisted fibre datum $\mathrm{dat} :$ `TwistedFibreDatum SS`, with uniformisers $\mathrm{unif}_1, \mathrm{unif}_2$, correction divisors $\mathrm{corr}_1, \mathrm{corr}_2$ and node constants $u_0, \lambda, \mu$ in $\kappa^{\times}$, subject to: `hunifFst` and `hunifSnd`, that $\mathrm{single}(s.1,1) + \mathrm{corr}_1(s)$ is the divisor of $\mathrm{unif}_1(s)$ and $\mathrm{single}(s.2,1) + \mathrm{corr}_2(s)$ that of $\mathrm{unif}_2(s)$, that both correction divisors vanish at both coordinates of every node pair, and that each has degree $-1$; `hu0`, that the modulus of the $s$-th annulus is $p^{e(s)}u$ with $u$ a unit of $A$ of residue $u_0(s)$; `hlam`, that whenever `flipParam SS An s` lies in the integers of $R_1$, the place $s.1$ takes the value $\lambda(s)$ on the quotient of its $R_1$-residue by $\mathrm{unif}_1(s)$; and `hmu`, the same for $\mathrm{param}$, $R_2$, $s.2$, $\mathrm{unif}_2(s)$ and $\mu(s)$.
--
--   (x) The divisor to be replaced: $X$ is a degree-zero divisor of $F_M$ over $\overline{\mathbb{Q}}$ which is invariant under the arithmetic action of the inertia subgroup of $A$ over $\mathbb{Q}$ (`hXst`) and each place in whose support is strict of the first kind, strict of the second kind, or has $\mathrm{red}_1$ equal to $s.1$ for some $s \in SS$ (`hXsupp`). A twist vector $a :$ `TwistVec ↥SS` is given with `ha : Psp.IsTwistOf α β hα hβ δ SS e An pos a X`, so that the degrees of the strict-first and strict-second parts of $X$ and its circle degrees along the annuli are the prescribed expressions in $a$. Finally `hadm` states that the twisted gluing datum `Psp.twistSpData α β hα hβ δ SS e An pos dat a X` is admissible (both divisor components of degree zero and vanishing at the relevant node coordinates), and `hsp` that its class in `GluedPic0 SS` is zero.
--
--   Under these hypotheses there exist a degree-zero divisor $D_2$ of $F_M$ over $\overline{\mathbb{Q}}$ and a proof that the plain gluing datum `Psp.glueData α β hα hβ δ SS D₂` (the pair of pushforwards of the strict-first and strict-second parts of $D_2$ along $\mathrm{red}_1$ and $\mathrm{red}_2$, with trivial node component) is admissible, such that, with respect to that membership: $D_2$ is a good divisor, that is, every place in its support is strict of the first or of the second kind; the class of its plain gluing datum in `GluedPic0 SS` is zero; and $D_2$ and $X$ have the same class in $\mathrm{Pic}^0$, i.e. `Pic0.mk D₂ = Pic0.mk X`.
--
--   This is the stable-chart step for $X_H(M)$ at a prime $p$ exactly dividing the level: it replaces a degree-zero, inertia-stable divisor of twist type whose twisted glued class vanishes by a linearly equivalent divisor supported only at strict places, with vanishing plain glued class. It is the form in which the vanishing of a glued Picard class is transported to a good representative, and it is used in the subsequent construction of inertia-fixed strict divisors with vanishing glued class modulo principal divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_gluedMk_eq_zero_pic0Mk_eq_of_isTwistOf_of_gluedMk_twistSpData_eq_zero_of_inertiaStable_of_annulus.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Definitions.Def_ModularCurve_JHTwistType
import Definitions.Def_ModularCurve_JHTwistedDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups
open Classical in

theorem ModularCurve.JHPlaceSpecialization.exists_isGoodDiv_gluedMk_eq_zero_pic0Mk_eq_of_isTwistOf_of_gluedMk_twistSpData_eq_zero_of_inertiaStable_of_annulus
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
        0 ≤ v.ord (Rpd.R₂.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS,
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
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
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
    (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)
    (hpos : JHPlaceSpecialization.AnnulusPositionLaw SS e An pos)
    (hposσ : ∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      pos s ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = pos s V)
    (hposD : ∀ (s : ↥SS) (d : ℕ), 0 < d → d < e s → ∃ V ∈ (An s).dom,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ pos s V = d)

    (dat : JHPlaceSpecialization.TwistedFibreDatum (p := p) (M := M) (H := H) (hpM := hpM) (A := A) SS)

    (hunifFst : ∀ s : ↥SS,
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (Finsupp.single (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1 (1 : ℤ) + dat.corrFst s) v = v.ord (dat.unifFst s)) ∧
      (∀ s' ∈ SS, dat.corrFst s s'.1 = 0 ∧ dat.corrFst s s'.2 = 0) ∧ Divisor.degree (dat.corrFst s) = -1)
    (hunifSnd : ∀ s : ↥SS,
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (Finsupp.single (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2 (1 : ℤ) + dat.corrSnd s) v = v.ord (dat.unifSnd s)) ∧
      (∀ s' ∈ SS, dat.corrSnd s s'.1 = 0 ∧ dat.corrSnd s s'.2 = 0) ∧ Divisor.degree (dat.corrSnd s) = -1)

    (hu0 : ∀ s : ↥SS, ∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u ∧ IsLocalRing.residue ↥A u = dat.u0 s)

    (hlam : ∀ (s : ↥SS) (h₁ : JHPlaceSpecialization.flipParam SS An s ∈ Rpd.R₁.integers),
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.HasValue
        ((Rpd.R₁.residue ⟨_, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) / dat.unifFst s) (dat.lam s : ResidueField ↥A))
    (hmu : ∀ (s : ↥SS) (h₂ : (An s).param ∈ Rpd.R₂.integers),
      (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.HasValue
        ((Rpd.R₂.residue ⟨_, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) / dat.unifSnd s) (dat.mu s : ResidueField ↥A))
    (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X)
    (hXsupp : ∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
      (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1))
    (a : JHPlaceSpecialization.TwistVec ↥SS)
    (ha : Psp.IsTwistOf α (θ.toAlgHom.comp α) hα hβ δ SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)))
    (hadm : Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS)
    (hsp : GluedPic0.mk SS ⟨Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm⟩ = 0) :
    ∃ (D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
      (hadm₂ : Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS),
      Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧
      GluedPic0.mk SS ⟨Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm₂⟩ = 0 ∧
      Pic0.mk D₂ = Pic0.mk X := by sorry
