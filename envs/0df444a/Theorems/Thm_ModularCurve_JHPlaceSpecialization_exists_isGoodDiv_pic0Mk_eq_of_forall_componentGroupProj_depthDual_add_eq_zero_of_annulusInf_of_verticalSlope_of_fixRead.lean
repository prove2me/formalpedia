-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_pic0Mk_eq_of_forall_componentGroupProj_depthDual_add_eq_zero_of_annulusInf_of_verticalSlope_of_fixRead
-- name    : ModularCurve.JHPlaceSpecialization.exists_isGoodDiv_pic0Mk_eq_of_forall_componentGroupProj_depthDual_add_eq_zero_of_annulusInf_of_verticalSlope_of_fixRead
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/b09edfd8-1d8d-5d7f-896a-0eab80982980
-- title:
--   Good representative of an inertia-fixed class with vanishing component reading
-- statement:
--   Fix a prime $p$ and a nonzero modulus $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$ (hypothesis `hHp`), and $M/p$ nonzero. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with `A.LiesOverPrime p`, i.e. $p$ is a nonunit of $A$, whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $F_M = \overline{\mathbb{Q}}\cdot F(X_H(M))$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field `xHFunctionField M H` inside Laurent series, $F_{M/p}$ for the corresponding field at level $M/p$ with the subgroup `infSubgroup p M H hpM` (the image of $H$ under reduction of units), and $\bar F =$ `Fbar p M H hpM κ` for the $q$-expansion function field over $\kappa$ at level `ΓN p M H hpM`.
--
--   The geometric data consist of: an automorphism $\theta$ of $F_M$ over $\overline{\mathbb{Q}}$; an integral $\overline{\mathbb{Q}}$-algebra map $\alpha : F_{M/p} \to F_M$ (hypothesis `hα`) with $\beta = \theta \circ \alpha$ integral (`hβ`), where $\alpha$ is the identity on underlying Laurent series (`hα_coe`) and $\beta$ acts on them by $q \mapsto q^p$, i.e. through `qExpand` at $p$ (`hβ_coe`); a unit $pb$ of $\mathbb{Z}/(M/p)$ reducing to $p$ (`hpb`); a self-map $\delta$ of the places of $\bar F$ over $\kappa$ which is the action of the mod-$p$ diamond automorphism attached to $pb$ through `diamondActionModL` and [`CuspForm.gammaLift`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) (`hδ`); a finite set $SS$ of pairs of places of $\bar F$ which is exactly `ssNodePairsQExp`, i.e. the set of pairs $s = (s_1,s_2)$ with $s_2$ supersingular and $s_1 = \mathrm{Frob}(s_2)$, where $\mathrm{Frob}$ is `qExpFrobeniusPlaceModL` (`hSS`); a specialisation $Psp$ of type `JHPlaceSpecialization p M H hpM A` (a map $sp$ from places of $F_{M/p}$ to places of $\bar F$ together with its $\mathrm{Pic}^0$-companion and the compatibilities recorded in that structure); and a prolongation datum $Rpd$ for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ from $F_M$ to $\bar F$ over $A$ with the $q$-expansion, $\theta$-transport and residue compatibilities of `ProlongationDatum`. Throughout, $\mathrm{red}_1 W = Psp.\mathtt{reduceFst}\,\alpha$ is $sp$ applied to the restriction of $W$ along $\alpha$, $\mathrm{red}_2 W = Psp.\mathtt{reduceSnd}\,\beta\,\delta$ is $\delta$ applied to $sp$ of the restriction along $\beta$; a place $v$ of $\bar F$ is `Fixed` when $\mathrm{Frob}(\delta(\mathrm{Frob}\,v)) = v$, and is an `IsAffinePlace` when it takes a value on an element whose expansion is the modular $j$-function in $q$; a place $W$ of $F_M$ is `IsStrictFst` when $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not `Fixed`, and `IsStrictSnd` when $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not `Fixed`; a divisor is `IsGoodDiv` when every place of its support is strict of one of the two kinds, and `fstDiv`, `sndDiv` are the restrictions of a divisor to the strict-first, resp. strict-second, places. `IsInftySide` and `IsZeroSide` single out the cuspidal places at which $q$-expansion ratio $x'/x^p$, resp. $x/x'^p$, has a value reducing to $1$.
--
--   The structural laws assumed are: `hFix`, that every supersingular place and its Frobenius translate are `Fixed`; `hTD`, the type dichotomy, that every place of $F_M$ satisfies $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hmodel`, the conjunction of the two divisor laws and the two cusp laws of `IsModel`; `hO`, the order law at `Fixed` affine places, reading $\mathrm{red}_1$-pushforwards of principal divisors as a sum of two residue orders; `hreg`, the regularity law for $SS$; `hnv`, the node value law for $SS$; `hθgal`, that $\theta$ commutes with the arithmetic Galois semilinear action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$; and `hFixFin`, that the locus of `Fixed` places of $\bar F$ is finite.
--
--   Two local hypotheses `hLFst` and `hLSnd` (one for each sheet) state: for distinct strict-first places $Q, Q'$ with the same first reading, that reading being an affine place, for a natural number $n$ nonzero in $\kappa$, for $g$ in the integers of $R_1$ with nonzero residue satisfying $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for all other strict-first places $W$ with that same reading, and for a presentation $g = 1 + e\,\varepsilon$ with $e \in A$ and $\varepsilon$ in the integers of $R_1$ with nonzero residue, the order of the $R_1$-residue of $\varepsilon$ at $\mathrm{red}_1 Q$ is at least $-1$; `hLSnd` is the same statement with $R_1, \mathrm{red}_1$, `IsStrictFst` replaced by $R_2, \mathrm{red}_2$, `IsStrictSnd`.
--
--   The hypothesis `hUnit` provides elements $u_1, u_2$ of $F_M$ and divisors $D_1, D_2$ with $D_i W = \mathrm{ord}_W u_i$ such that: $u_1$ and $u_1^{-1}$ lie in the integers of $R_1$, the residue of $u_1$ is nonzero, the $\mathrm{red}_1$-pushforward of the strict-first part of $D_1$ computes the order of that residue at every place of $\bar F$ which is not `Fixed`, and the $\mathrm{red}_1$-pushforward of the `IsInftySide` part of $D_1$ computes it at the reading of every `IsInftySide` place; moreover every nonzero $f$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j}$ in the integers of $R_2$ with nonzero residue; and symmetrically for $u_2$, $D_2$, $R_2$, $\mathrm{red}_2$ and the `IsZeroSide` places, with every nonzero $f$ admitting $f^m u_2^{\,j}$ of nonzero $R_1$-residue. The hypothesis `hcusp` states that every non-affine place of $\bar F$ is the $\mathrm{red}_1$-reading of some `IsInftySide` place and the $\mathrm{red}_2$-reading of some `IsZeroSide` place, while `horientInf` and `horient0` orient the cuspidal readings: $\delta(\mathrm{Frob}(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for $C$ on the $\infty$-side and $\mathrm{red}_1 C = \mathrm{Frob}(\mathrm{red}_2 C)$ for $C$ on the zero-side.
--
--   Next, a width function $e : SS \to \mathbb{N}$ with $e(s) > 0$ (`he`) is given, together with the annulus hypothesis `hAnn`: for each node $s$ there exists an [`AlgebraicCurve.Annulus`](def/AlgebraicCurve_SemistableCharts.html#L86) $An$ over $A$ in $F_M$ — a domain of places, a parameter and a modulus in the maximal ideal of $A$ subject to the axioms of that structure (rationality of the places of the domain, the parameter taking a nonzero value in the maximal ideal with the modulus factoring through it, a unique place of the domain for each admissible value, $\mathrm{ord}(\mathrm{param} - \mathrm{value}) = 1$, and a unit principle) — whose domain is exactly the set of places $W$ with $\mathrm{red}_1 W = s_1$ that are strict of neither kind, whose modulus is $p^{e(s)}$ times a unit of $A$, whose parameter is invariant under the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb{Q}$, for which $\mathrm{modulus}^{-1}\cdot\mathrm{param}$ lies in the integers of $R_1$ and $\mathrm{param}$ lies in the integers of $R_2$ with nonzero residue, and which is attached at both ends: the $R_2$-residue of $\mathrm{param}$ has order $1$ at $s_2$ and, for every $f$ in the integers of $R_2$ with nonzero residue and $\mathrm{ord}_P f = 0$ on the domain, $P.\mathtt{evalAt}\,f \cdot (P.\mathtt{evalAt}\,\mathrm{param})^{-\mathrm{ord}_{s_2}(\mathrm{res}_2 f)}$ is a unit of $A$ for every $P$ of the domain; symmetrically the $R_1$-residue of $\mathrm{modulus}\cdot\mathrm{param}^{-1}$ has order $1$ at $s_1$ with the corresponding unit statement on the first sheet.
--
--   The vertical-slope hypothesis `hVSlope` asserts: for every family $An : SS \to$ annuli satisfying, for each $s$, all the conditions just listed, and for every $k \in \mathbb{N}$ divisible by all $e(s)$, there exist $f \in F_M$ and $c \in \overline{\mathbb{Q}}$ with $c \cdot f$ in the integers of $R_1$ such that $f \neq 0$, the $R_1$-residue of $c\cdot f$ is nonzero, every divisor $G$ with $G V = \mathrm{ord}_V f$ is a good divisor, $\mathrm{ord}_V f = 0$ for every place $V$ whose first reading is `Fixed` and differs from all $s_1$ with $s \in SS$, the order of the residue of $c \cdot f$ vanishes at every `Fixed` place of $\bar F$ distinct from all $s_1$, and for each node $s$ there is $a \neq 0$ in $\overline{\mathbb{Q}}$ with $\mathrm{ord}_P f = 0$ and $P.\mathtt{evalAt}\,f \cdot a \cdot (P.\mathtt{evalAt}(An\,s).\mathrm{param})^{-k/e(s)}$ a unit of $A$ for all $P$ in the domain of $An\,s$.
--
--   Further reading hypotheses are assumed. `hFixReadFst` and `hFixReadSnd`: for $g$ of nonzero $R_i$-residue and $v$ a `Fixed` place distinct from all first (resp. second) coordinates of nodes, if $\mathrm{ord}_V g = 0$ for every $V$ with $\mathrm{red}_i V = v$, then the order of the $R_i$-residue of $g$ at $v$ vanishes. `hFixRegFst` and `hFixRegSnd`: the same with `IsAffinePlace` imposed on $v$ and with the inequalities $0 \le \mathrm{ord}_V g$ in place of the equalities, concluding $0 \le \mathrm{ord}_v(\mathrm{res}_i g)$. The four one-sided laws `hOSFst`, `hOSSnd`, `hOSInf`, `hOSZero` state, for $g$ of nonzero residue on the respective sheet and $E$ the divisor of $g$: that the $\mathrm{red}_1$-pushforward of the strict-first part of $E$, resp. the $\mathrm{red}_2$-pushforward of the strict-second part, computes the order of the corresponding residue at every non-`Fixed` place of $\bar F$; and that the $\mathrm{red}_1$-pushforward of the `IsInftySide` part, resp. the $\mathrm{red}_2$-pushforward of the `IsZeroSide` part, computes that order at the reading of every `IsInftySide`, resp. `IsZeroSide`, place.
--
--   Finally, a weight function $\mathrm{depth}$ on the places of $F_M$ is given, subject to `hdepth`: for every node $s$ and every annulus $An$ satisfying the attachment conditions of `hAnn`, the law `AnnulusDepthLawInf` holds, namely for every inertia-invariant place $V$ with $\mathrm{red}_1 V = s_1$ one has $A$-valuation of $V.\mathtt{evalAt}(\mathrm{modulus}\cdot\mathrm{param}^{-1})$ equal to the $A$-valuation of $p$ raised to $\mathrm{depth}\,V$. The family hypothesis `hFam` asserts that for every finite set $B$ of places of $\bar F$ and all $m_1, m_2$ there are families $Q_1 : \mathrm{Fin}\,m_1$ and $Q_2 : \mathrm{Fin}\,m_2$ of places of $F_M$, strict of the first, resp. second, kind, with injective first, resp. second, readings, all readings outside $B$, and all members invariant under the arithmetic Galois action of the inertia subgroup of $A$.
--
--   Let $D$ be a divisor of degree zero on the places of $F_M$ over $\overline{\mathbb{Q}}$ such that (`hDfix`) every place $V$ of its support is invariant under the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb{Q}$, and is strict-first, or strict-second, or satisfies $\mathrm{red}_1 V = s_1$ for some $s \in SS$. Assume further (`hread`) that for every node $s_0 \in SS$ the image under `componentGroupProj e` — the quotient of the dual of the character lattice of $SS$ by the range of `gramMap e` — of the functional
--   $$Psp.\mathtt{depthDual}\,\alpha\,h\alpha\,SS\,\mathrm{depth}\,D \;+\; \deg\bigl(Psp.\mathtt{sndDiv}\,\alpha\,\beta\,h\alpha\,h\beta\,\delta\,D\bigr)\cdot\bigl(e(s_0)\cdot \mathtt{crossingCoord}\,s_0\bigr)$$
--   vanishes; here `depthDual` is the sum over $s \in SS$ of $Psp.\mathtt{depthDiv}\,\alpha\,h\alpha\,\mathrm{depth}\,D\,s_1$ times the coordinate functional `crossingCoord s`, and the second term is the degree of the strict-second part of $D$ times $e(s_0)$ times the coordinate functional at $s_0$.
--
--   The conclusion is that there exists a divisor $D'$ of degree zero on the places of $F_M$ over $\overline{\mathbb{Q}}$ such that $D'$ is a good divisor, i.e. every place of its support is strict-first or strict-second, and $D'$ has the same class as $D$ in $\mathrm{Pic}^0$, i.e. `Pic0.mk D' = Pic0.mk D`.
--
--   This is the subtraction step in the component-group analysis of $J_H(M)$ at a prime $p$ with $p \parallel M$, in the style of Raynaud's description of the special fibre of the Picard functor: a degree-zero class whose depth reading dies in the component group of the supersingular crossing lattice is shown to be represented by a divisor supported away from the crossings. It feeds the companion statement in which the component-group reading is replaced by a composition hypothesis and a depth-composition law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_pic0Mk_eq_of_forall_componentGroupProj_depthDual_add_eq_zero_of_annulusInf_of_verticalSlope_of_fixRead.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_isGoodDiv_pic0Mk_eq_of_forall_componentGroupProj_depthDual_add_eq_zero_of_annulusInf_of_verticalSlope_of_fixRead
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

    (hOSFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ E) v = v.ord (Rpd.R₁.residue ⟨g, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hOSSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ E) v = v.ord (Rpd.R₂.residue ⟨g, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hOSInf : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) c →
          Finsupp.mapDomain (Psp.reduceFst α hα) (E.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα c) =
            (Psp.reduceFst α hα c).ord (Rpd.R₁.residue ⟨g, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hOSZero : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) c →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (E.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ c) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ c).ord (Rpd.R₂.residue ⟨g, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (depth : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℕ)
    (hdepth : ∀ (s : ↥SS) (An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H)),
      ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
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
                (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))) →
      Psp.AnnulusDepthLawInf α hα (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) An depth)

    (hFam : ∀ (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (m₁ m₂ : ℕ),
      ∃ (Q₁ : Fin m₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂ : Fin m₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
        (∀ i, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (Q₁ i)) ∧ (∀ j, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ (Q₂ j)) ∧
        (Function.Injective fun i => Psp.reduceFst α hα (Q₁ i)) ∧
        (Function.Injective fun j => Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (Q₂ j)) ∧
        (∀ i, Psp.reduceFst α hα (Q₁ i) ∉ B) ∧ (∀ j, Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (Q₂ j) ∉ B) ∧
        (∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • Q₁ i = Q₁ i) ∧
        (∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • Q₂ j = Q₂ j))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hDfix : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
          (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧
        (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨
          ∃ s ∈ SS, Psp.reduceFst α hα V = s.1))
    (hread : ∀ s₀ : ↥SS,
      componentGroupProj e
          (Psp.depthDual α hα SS depth (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) +
            Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) •
              ((e s₀ : ℤ) • crossingCoord s₀)) = 0) :
    ∃ D' : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D' : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧
        Pic0.mk D' = Pic0.mk D := by sorry
