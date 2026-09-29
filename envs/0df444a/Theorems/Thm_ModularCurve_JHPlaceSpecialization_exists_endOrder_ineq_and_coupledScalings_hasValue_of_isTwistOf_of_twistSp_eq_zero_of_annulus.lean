-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_twistSp_eq_zero_of_annulus
-- name    : ModularCurve.JHPlaceSpecialization.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_twistSp_eq_zero_of_annulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/5b0a64b1-6669-5439-85dc-ee5b05ea468c
-- title:
--   Chord bounds and rigidity of coupled sheet scalings at supersingular nodes
-- statement:
--   **Setting.** Let $p$ be a prime and $M$ a positive integer with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is trivial (`hHp`). Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ in which $p$ is a non-unit (`hA`, i.e. `A.LiesOverPrime p`), with residue field $\kappa =$ `ResidueField ↥A` of characteristic $p$ and algebraically closed. Write $F =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$, inside $\overline{\mathbb{Q}}((q))$, of the $q$-expansion function field of $X_H(M)$, $F' =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ for the image subgroup `infSubgroup p M H hpM` $=$ image of $H$ in $(\mathbb{Z}/(M/p))^\times$, and $\bar F =$ `Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ attached to the congruence subgroup `ΓN p M H hpM`.
--
--   The data are: an automorphism $\theta$ of $F$ over $\overline{\mathbb{Q}}$; an $\overline{\mathbb{Q}}$-algebra map $\alpha : F' \to F$ with $\alpha$ integral (`hα`) and $\beta := \theta \circ \alpha$ integral (`hβ`), where $\alpha$ is the identity on underlying Laurent series (`hα_coe`) and $\beta$ is the substitution $q \mapsto q^p$, i.e. `qExpand … p`, on underlying Laurent series (`hβ_coe`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`); a self-map $\delta$ of the places of $\bar F$ over $\kappa$, given by the pointwise action of the semilinear automorphism `SemilinearAut.ofAlgAut` of the diamond automorphism `diamondActionModL` at level $M/p$ for `infSubgroup p M H hpM`, evaluated at a lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$ to $\Gamma_0(M/p)$ (`hδ`); a finite set $SS$ of pairs of places of $\bar F$ which is exactly the set `ssNodePairsQExp` of supersingular node pairs, i.e. pairs $s = (s_1,s_2)$ with $s_2$ supersingular and $s_1 = \mathrm{Frob}(s_2)$ for the $q$-expansion Frobenius `qExpFrobeniusPlaceModL` (`hSS`); a place specialisation $P_{\mathrm{sp}} =$ `Psp` of type `JHPlaceSpecialization p M H hpM A`, carrying the reduction map `sp` from places of $F'$ to places of $\bar F$ together with its divisor, surjectivity, inertia and Frobenius axioms; and a prolongation datum $R_{\mathrm{pd}} =$ `Rpd` for `Psp` and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F$ with residue maps to $\bar F$, compatible through $\theta$.
--
--   Throughout, $\mathrm{reduceFst}(W) =$ `Psp.sp` of the restriction of $W$ along $\alpha$, and $\mathrm{reduceSnd}(W) = \delta($`Psp.sp` of the restriction of $W$ along $\beta)$; a place $W$ of $F$ is *strict first* when $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$ and $\mathrm{reduceFst}\,W$ is not `Fixed` (i.e. $\mathrm{Frob}(\delta(\mathrm{Frob}\,v)) \ne v$), and *strict second* when $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ and $\mathrm{reduceSnd}\,W$ is not `Fixed`; `fstDiv` and `sndDiv` are the restrictions of a divisor to the strict-first, resp. strict-second, places.
--
--   **Hypotheses, by group.** (i) Fixed-point and dichotomy hypotheses: `hFix` (every supersingular place of $\bar F$ and its Frobenius image are `Fixed` for $\delta$), `hTD` (`TypeDichotomy`: every place $W$ of $F$ satisfies $\mathrm{reduceFst}\,W = \mathrm{Frob}(\mathrm{reduceSnd}\,W)$ or $\delta(\mathrm{Frob}(\mathrm{reduceFst}\,W)) = \mathrm{reduceSnd}\,W$), and `hFixFin` (the set of $\delta$-`Fixed` places of $\bar F$ is finite).
--
--   (ii) The model laws for $R_{\mathrm{pd}}$: `hmodel` (`IsModel`, the conjunction of the two divisor laws, computing the pushforwards along $\mathrm{reduceFst}$, $\mathrm{reduceSnd}$ of `fstDiv`, `sndDiv` of a principal divisor as orders of the corresponding residues at non-`Fixed` places, and the two cusp laws for the infinity and zero sides), `hO` (`OrderLawFixed`: at a `Fixed` affine place the pushforward of the full divisor splits as the order of the first residue plus the order of the second residue at $\delta(\mathrm{Frob}\,v)$), `hreg` (`RegularityLaw`, two clauses: positivity of the residue orders at `Fixed` affine places, and existence of a common value of the two residues at node pairs), and `hnv` (`NodeValueLaw`: a common non-zero value of the two residues at a node whose two branches carry no zeros or poles of $f$). Here `IsAffinePlace v` means that some element of $\bar F$ with $q$-expansion `jqModC` has a value at $v$.
--
--   (iii) Galois compatibility: `hθgal`, stating that $\theta$ commutes with the arithmetic Galois action `arithmeticGalois` of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F$.
--
--   (iv) Two-point local laws `hLFst` and `hLSnd` (mirror images of one another): if $Q \ne Q'$ are strict-first places with the same, affine, reduction, $n$ a natural number non-zero in $\kappa$, $g \in R_1$ with non-zero residue, $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict-first $W$ with the same reduction, and if $g = 1 + e\varepsilon$ with $e \in A$ and $\varepsilon \in R_1$ of non-zero residue, then the common reduction place has order $\ge -1$ on the residue of $\varepsilon$; `hLSnd` is the same statement for strict-second places, $\mathrm{reduceSnd}$ and $R_2$.
--
--   (v) Unit hypothesis `hUnit`: there are $u_1, u_2 \in F$ with divisors $D_1, D_2$ such that $u_1$ and $u_1^{-1}$ lie in $R_1$ with $\mathrm{res}_1 u_1 \ne 0$, the pushforward along $\mathrm{reduceFst}$ of the strict-first part of $D_1$ computes the order of $\mathrm{res}_1 u_1$ at every non-`Fixed` place, and the pushforward of the infinity-side part of $D_1$ computes its order at the reductions of infinity-side places; symmetrically for $u_2$, $R_2$, $\mathrm{reduceSnd}$ and the zero side; and every non-zero $f \in F$ admits $m \ne 0$ and $j \in \mathbb{Z}$ with $f^m u_1^j$ a unit of $R_2$ (respectively $f^m u_2^j$ a unit of $R_1$), in the sense of lying in the integers with non-zero residue.
--
--   (vi) Cusp hypotheses: `hcusp` (every non-affine place of $\bar F$ is the $\mathrm{reduceFst}$-image of an infinity-side place and the $\mathrm{reduceSnd}$-image of a zero-side place) and the orientation laws `horientInf` ($\delta(\mathrm{Frob}(\mathrm{reduceFst}\,C)) = \mathrm{reduceSnd}\,C$ for $C$ on the infinity side) and `horient0` ($\mathrm{reduceFst}\,C = \mathrm{Frob}(\mathrm{reduceSnd}\,C)$ for $C$ on the zero side).
--
--   (vii) Annuli: positive integers $e(s)$ for $s \in SS$ (`he`), and `hAnn`, asserting for each $s$ the existence of an annulus `Annulus A F` whose domain consists exactly of the places reducing under $\mathrm{reduceFst}$ to $s_1$ that are neither strict first nor strict second, whose modulus is $p^{e(s)}$ times a unit of $A$, whose parameter is fixed by the inertia subgroup `A.inertiaSubgroupIn ℚ` acting through `arithmeticGalois`, and which satisfies: $(\text{modulus})^{-1} \cdot \mathrm{param} \in R_1$; $\mathrm{param} \in R_2$ with non-zero residue; $\mathrm{ord}_{s_2}(\mathrm{res}_2\,\mathrm{param}) = 1$ together with the unit principle that for $f \in R_2$ of non-zero residue and of order $0$ on the annulus, $\mathrm{ev}_P(f)\,\mathrm{ev}_P(\mathrm{param})^{-\mathrm{ord}_{s_2}(\mathrm{res}_2 f)}$ is a unit of $A$ at every $P$ in the domain; and the mirror clause for the flipped parameter $(\text{modulus})\cdot\mathrm{param}^{-1} \in R_1$ at $s_1$. A chosen family `An` with exactly these properties is provided by `hAn`.
--
--   (viii) Reading-off and regularity at `Fixed` non-node places: `hFixReadFst`, `hFixReadSnd` (if $g$ is a unit of $R_1$, resp. $R_2$, and $v$ is `Fixed`, distinct from all first, resp. second, members of nodes, and $g$ has order $0$ at all places above $v$, then the residue of $g$ has order $0$ at $v$) and `hFixRegFst`, `hFixRegSnd` (the same with 'order $0$' replaced by 'order $\ge 0$', for $v$ in addition affine).
--
--   (ix) Slope hypothesis `hVSlope`: for every family of annuli with the list of properties in (vii) and every $k$ divisible by all $e(s)$, there is a non-zero $f \in F$ and $c \in \overline{\mathbb{Q}}$ with $c\cdot f$ a unit of $R_1$, whose divisor is a good divisor (supported on strict places), which has order $0$ at every place whose first reduction is `Fixed` and is not the first member of a node, whose $R_1$-residue has order $0$ at every such `Fixed` non-node place of $\bar F$, and such that for each $s$ there is $a \ne 0$ with $\mathrm{ord}_P f = 0$ and $\mathrm{ev}_P(f)\,a\,\mathrm{ev}_P(\mathrm{param})^{-(k/e(s))}$ a unit of $A$ for all $P$ in the $s$-th annulus.
--
--   (x) Positions: a function `pos` assigning to each node $s$ and each place of $F$ a rational number, satisfying `hpos` (`AnnulusPositionLaw`: on the $s$-th annulus $0 < \mathrm{pos}\,s\,V < e(s)$ and the valuation of the flipped parameter at $V$ is the prescribed fractional power of the valuation of $p$), `hposσ` (invariance of `pos` under the inertia action) and `hposD` (for every integer $d$ with $0 < d < e(s)$ there is an inertia-fixed place of the $s$-th annulus with $\mathrm{pos}\,s\,V = d$).
--
--   (xi) The twisted fibre datum `dat` for $SS$: uniformisers $\mathrm{unifFst}(s), \mathrm{unifSnd}(s) \in \bar F$, correction divisors $\mathrm{corrFst}(s), \mathrm{corrSnd}(s)$ and units $u_0(s), \lambda(s), \mu(s)$ of $\kappa$, subject to: `hunifFst` and `hunifSnd` (the divisor of $\mathrm{unifFst}(s)$ is $\delta_{s_1} + \mathrm{corrFst}(s)$, $\mathrm{corrFst}(s)$ vanishes at both members of every node and has degree $-1$; likewise for $\mathrm{unifSnd}(s)$, $\delta_{s_2}$, $\mathrm{corrSnd}(s)$), `hu0` (the unit part of the $s$-th modulus reduces to $u_0(s)$), `hlam` (the first place $s_1$ takes the value $\lambda(s)$ on $\mathrm{res}_1(\mathrm{flipParam}\,s)/\mathrm{unifFst}(s)$) and `hmu` ($s_2$ takes the value $\mu(s)$ on $\mathrm{res}_2(\mathrm{param})/\mathrm{unifSnd}(s)$).
--
--   (xii) The twist: a degree-zero divisor $X$ on $F$, stable under the inertia action (`hXst`) and supported on strict-first places, strict-second places and places whose first reduction is the first member of a node (`hXsupp`); a twist vector $a$ (data $a_Z, a_{Z'} \in \mathbb{Z}$ and $a_E : SS \times \mathbb{N} \to \mathbb{Z}$) with `ha` : `Psp.IsTwistOf … a X`, i.e. the degrees of the strict-first and strict-second parts of $X$ are the negatives of the sums over $s$ of the end orders $o_1(s) =$ `twistEndOrderFst … a X s` and $o_2(s) =$ `twistEndOrderSnd … a X s`, and for $1 \le d \le e(s)-1$ the circle degree `twistCircleDeg … X s d` equals minus the second difference of the chain values of $a$ at $d$. Here $o_1(s)$ is the difference of the chain values of $a$ at $1$ and $0$ plus the integral part of the circle degree at $0$, and $o_2(s)$ is the difference of the chain values at $e(s)-1$ and $e(s)$ plus the integral part of the circle degree at $e(s)$. Finally `hadm` states that the gluing datum `Psp.twistSpData … dat a X` — whose three slots are the $\mathrm{reduceFst}$-pushforward of the strict-first part of $X$ corrected by $-\sum_s o_1(s)\,\mathrm{corrFst}(s)$, the $\mathrm{reduceSnd}$-pushforward of the strict-second part corrected by $-\sum_s o_2(s)\,\mathrm{corrSnd}(s)$, and the node unit family `twistNodeUnit` — is admissible (both divisors of degree zero and vanishing at the respective node members), and `hsp` states that its class in `GluedPic0 SS` is zero.
--
--   (xiii) The function: natural numbers $d_1, d_2$, families $Q_1 : \mathrm{Fin}\,d_1 \to$ places of $F$ all strict first (`hQ₁`) and $Q_2 : \mathrm{Fin}\,d_2 \to$ places of $F$ all strict second (`hQ₂`), an effective divisor $E \ge 0$, and a non-zero $f \in F$ with
--   $$\mathrm{div}(f) = E - \Big(\sum_i \delta_{Q_1(i)} + \sum_j \delta_{Q_2(j)}\Big) - X \qquad (\mathtt{hdivf}).$$
--
--   **Conclusion.** There exists $\delta' \in \mathbb{Q}$ with the following three properties.
--
--   1.
--
--   For every $c \in \overline{\mathbb{Q}}$ such that $c \cdot f$ lies in the integers of $R_1$ with non-zero residue, and every $s \in SS$,
--   $$\delta' \le e(s)\,\big(\mathrm{ord}_{s_1}\big(\mathrm{res}_1(c\cdot f)\big) + o_1(s)\big).$$
--
--   2.
--
--   For every $c \in \overline{\mathbb{Q}}$ such that $c \cdot f$ lies in the integers of $R_2$ with non-zero residue, and every $s \in SS$,
--   $$-\,e(s)\,\big(\mathrm{ord}_{s_2}\big(\mathrm{res}_2(c\cdot f)\big) + o_2(s)\big) \le \delta'.$$
--
--   3.
--
--   There are $c_1, c_2 \in \overline{\mathbb{Q}}$ with $c_1 \cdot f$ in the integers of $R_1$ and $c_2 \cdot f$ in the integers of $R_2$, both residues non-zero, such that: for all $g_1, g_2 \in \bar F$ and all families $a_v, b_v : SS \to \kappa^\times$ for which the first slot of `Psp.twistSpData … dat a X` is the divisor of $g_1$, the second slot is the divisor of $g_2$, each $s$ satisfies $s_1$ has value $a_v(s)$ on $g_1$ and $s_2$ has value $b_v(s)$ on $g_2$, and the third slot is $s \mapsto$ `Additive.ofMul` $(a_v(s)/b_v(s))$, the following holds at every $s \in SS$: if $\delta' = 0$ and
--   $$\mathrm{ord}_{s_2}\big(\mathrm{res}_2(c_2 \cdot f)\big) + o_2(s) = 0,$$
--   then
--   $$\mathrm{ord}_{s_1}\big(\mathrm{res}_1(c_1 \cdot f)\big) + o_1(s) = 0$$
--   and there is a unit $c$ of $\kappa$ which is simultaneously the value at $s_1$ of
--   $$\mathrm{res}_1(c_1 \cdot f)\; g_1 \prod_{s' \in SS} \mathrm{unifFst}(s')^{\,o_1(s')}$$
--   and the value at $s_2$ of
--   $$\mathrm{res}_2(c_2 \cdot f)\; g_2 \prod_{s' \in SS} \mathrm{unifSnd}(s')^{\,o_2(s')},$$
--   where 'has value $c$' means, as in `Place.HasValue`, membership in the valuation ring of the place together with residue equal to the image of $c$.
--
--   This is the $\Gamma_H$-level statement, for $p$ exactly dividing $M$, of the chord-versus-end-slope inequalities for the Gauss profiles of a function $f$ along the supersingular annuli of $X_H(M)$ at $p$, together with the rigidity of one coupled pair of scalings of $f$ on the two sheets: when the glued class of the twisted gluing datum vanishes and the second-sheet end order is flat, the first-sheet end order is flat too and the two corrected residues take one common value at the node. It feeds the computation of the pushforwards of the strict-first and strict-second parts of a divisor in [`ModularCurve.JHPlaceSpecialization.mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq_of_twistSp_eq_zero_of_pin`](thm.html#ModularCurve.JHPlaceSpecialization.mapDomain_fstDiv_eq_and_mapDomain_sndDiv_eq_of_twistSp_eq_zero_of_pin), part of the analysis of the semistable fibre of the modular curve at $p$ and of the specialisation of divisor classes on it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_twistSp_eq_zero_of_annulus.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_endOrder_ineq_and_coupledScalings_hasValue_of_isTwistOf_of_twistSp_eq_zero_of_annulus
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
    (hsp : GluedPic0.mk SS ⟨Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm⟩ = 0)

    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hQ₁ : ∀ i, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (Q₁ i)) (hQ₂ : ∀ j, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ (Q₂ j))
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hE0 : 0 ≤ E)
    (f : ↥(xHFunctionFieldBar M H)) (hf0 : f ≠ 0)
    (hdivf : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) V = V.ord f) :
    ∃ δ' : ℚ,

      (∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • f, h⟩ ≠ 0 →
        ∀ s : ↥SS, δ' ≤ (e s : ℚ) * ((((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c • f, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : ℤ) : ℚ) + (JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s : ℚ))) ∧

      (∀ (c : AlgebraicClosure ℚ) (h : c • f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨c • f, h⟩ ≠ 0 →
        ∀ s : ↥SS, -((e s : ℚ) * ((((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨c • f, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : ℤ) : ℚ) + (JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s : ℚ))) ≤ δ') ∧

      (∃ (c₁ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ Rpd.R₁.integers) (c₂ : AlgebraicClosure ℚ) (h₂ : c₂ • f ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0 ∧
        ∀ (g₁ g₂ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (av bv : ↥SS → (ResidueField ↥A)ˣ),
          (∀ v, (Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).1 v = v.ord g₁) →
          (∀ v, (Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).2.1 v = v.ord g₂) →
          (∀ s : ↥SS,
            (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.HasValue g₁ (av s) ∧ (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.HasValue g₂ (bv s)) →
          ((Psp.twistSpData α (θ.toAlgHom.comp α) hα hβ δ SS e An pos dat a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))).2.2 = fun s => Additive.ofMul (av s / bv s)) →
          ∀ s : ↥SS, δ' = 0 →
            (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.ord (Rpd.R₂.residue ⟨c₂ • f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) + JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s = 0 →
            ((s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.ord (Rpd.R₁.residue ⟨c₁ • f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) + JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s = 0 ∧
             ∃ c : (ResidueField ↥A)ˣ,
               (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).1.HasValue
                 ((Rpd.R₁.residue ⟨c₁ • f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) * g₁ * ∏ s' : ↥SS, dat.unifFst s' ^ JHPlaceSpecialization.twistEndOrderFst SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s') (c : ResidueField ↥A) ∧
               (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).2.HasValue
                 ((Rpd.R₂.residue ⟨c₂ • f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) * g₂ * ∏ s' : ↥SS, dat.unifSnd s' ^ JHPlaceSpecialization.twistEndOrderSnd SS e An pos a (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) s') (c : ResidueField ↥A))) := by sorry
