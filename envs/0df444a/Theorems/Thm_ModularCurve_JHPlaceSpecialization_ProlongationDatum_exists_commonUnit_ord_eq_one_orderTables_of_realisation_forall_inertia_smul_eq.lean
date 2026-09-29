-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_ord_eq_one_orderTables_of_realisation_forall_inertia_smul_eq
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_ord_eq_one_orderTables_of_realisation_forall_inertia_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/e816686c-9add-53da-ac03-e2a66dd3666c
-- title:
--   Inertia-equivariant common unit with prescribed simple zero and order tables
-- statement:
--   **The data.** $p$ is a prime and $M$ a nonzero natural number with $p \mid M$ and $p^{2} \nmid M$; $H$ is a subgroup of $(\mathbb Z/M)^{\times}$ which, by the hypothesis `hHp`, contains every unit whose image under the reduction $(\mathbb Z/M)^{\times}\to(\mathbb Z/(M/p))^{\times}$ is trivial, and $M/p$ is nonzero. $A$ is a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$ (this is `A.LiesOverPrime p`), whose residue field $\kappa=\mathrm{ResidueField}\,A$ has characteristic $p$ and is algebraically closed. Write $F_M$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb Q}$ of the $q$-expansion function field of $X_H(M)$ inside $\overline{\mathbb Q}((q))$, $F_{M/p}$ for `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, where `infSubgroup` is the image of $H$ in $(\mathbb Z/(M/p))^{\times}$, and $\bar F$ for `Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ at level `ΓN p M H hpM`. Places are `Place`-structures (valuation subrings containing the base field, not everything, with principal maximal ideal), $\operatorname{ord}_v$ is the associated normalised order function, and $\varphi$ denotes `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`, the restriction of places along the mod-$p$ $q$-expansion Frobenius of $\bar F$.
--
--   Further data: $\theta$ is an $\overline{\mathbb Q}$-algebra automorphism of $F_M$; $\alpha\colon F_{M/p}\to F_M$ is an integral $\overline{\mathbb Q}$-algebra map, and $\beta:=\theta\circ\alpha$ is integral as well ($\hbar\alpha$, $\hbar\beta$); the two **$q$-expansion pins** `hα_coe` and `hβ_coe` say that the Laurent series of $\alpha u$ is that of $u$, while the Laurent series of $\beta u$ is `qExpand p` applied to that of $u$ (i.e. $q\mapsto q^{p}$). `pb` is a unit of $\mathbb Z/(M/p)$ whose underlying element is $p$, and $\delta$ is a self-map of the places of $\bar F$ required by `hδ` to be the action of the semilinear automorphism attached to `diamondActionModL κ (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) pb)`, i.e. to the reduced diamond operator $\langle p\rangle$ at level $M/p$. $SS$ is a finite set of pairs of places of $\bar F$ which by `hSS` is exactly `ssNodePairsQExp κ (ΓN p M H hpM) p`: the pairs $s$ with $s.2$ supersingular and $s.1=\varphi(s.2)$. `Psp` is a `JHPlaceSpecialization p M H hpM A` (a specialization map `sp` from places of $F_{M/p}$ to places of $\bar F$ together with a map on degree-zero divisor classes and the compatibility axioms `d0_qexp`, `d4`, `d5`, `d6_inertia`, `d6_frobenius`, `spPic0_compat`), and `Rpd` is a `ProlongationDatum Psp θ`: two regular prolongations $R_1,R_2$ of $A$ to $F_M$ with residue field $\bar F$, the clause `residue₁_coeffMap` computing the $R_1$-residue of a Laurent series with coefficients in $A$ coefficientwise, and the clauses `mem_integers₂_iff`, `residue₂_eq` identifying $R_2$ with the $\theta$-transport of $R_1$. Throughout, $r_1(W):=$ `Psp.reduceFst α hα W` $=\mathrm{sp}(W|_{\alpha})$ and $r_2(W):=$ `Psp.reduceSnd β hβ δ W` $=\delta(\mathrm{sp}(W|_{\beta}))$ are the two readings of a place $W$ of $F_M$ on $\bar F$; $W$ is strict-first (`IsStrictFst`) when $\delta(\varphi(r_1W))=r_2W$ and $r_1W$ is not $\delta$-fixed, strict-second (`IsStrictSnd`) when $r_1W=\varphi(r_2W)$ and $r_2W$ is not $\delta$-fixed; a place $v$ of $\bar F$ is `Fixed` when $\varphi(\delta(\varphi(v)))=v$, and `IsAffinePlace` when some $x\in\bar F$ with Laurent series `jqModC κ` has a value in $\kappa$ at $v$.
--
--   **The hypotheses.** They fall into the following groups, each stated in full or summarised as indicated.
--
--   *Fixedness at the supersingular places* (`hFix`): for every $y\in$ `ssPlacesQExp κ (ΓN p M H hpM) p`, both $y$ and $\varphi(y)$ are `Fixed` for $\delta$. *Finiteness* (`hFixFin`): the set of $\delta$-fixed places of $\bar F$ is finite.
--
--   *The law block.* `hTD` (`TypeDichotomy`): every place $W$ of $F_M$ satisfies $r_1W=\varphi(r_2W)$ or $\delta(\varphi(r_1W))=r_2W$. `hmodel` (`IsModel`): the conjunction of the four laws `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty`, `CuspLawZero` of the prolongation datum. `hO` (`OrderLawFixed`): for $f\in F_M$ lying in both rings of integers with both residues nonzero and $D=\operatorname{div} f$ pointwise, and for every `Fixed` affine place $v$, the pushforward $(r_1)_*D$ at $v$ equals $\operatorname{ord}_v(\bar f_1)+\operatorname{ord}_{\delta(\varphi(v))}(\bar f_2)$. `hreg` (`RegularityLaw`, two clauses): first, for $f$ in both rings of integers and $v$ a `Fixed` affine place such that $\operatorname{ord}_Vf\ge 0$ for every $V$ with $r_1V=v$, the orders $\operatorname{ord}_v(\bar f_1)$ and $\operatorname{ord}_{\delta(\varphi(v))}(\bar f_2)$ are $\ge 0$ whenever the respective residues are nonzero; second, for $s\in SS$ with $\operatorname{ord}_Vf\ge0$ for every $V$ with $r_1V=s.1$, the residues $\bar f_1,\bar f_2$ take a common value $c\in\kappa$ at $s.1$ and $s.2$. `hnv` (`NodeValueLaw`): for $f$ in both rings of integers with nonzero residues and $s\in SS$ such that no $V$ with $\operatorname{ord}_Vf\neq0$ has $(r_1V,r_2V)=(s.1,s.2)$, the residues take a common nonzero value at $s.1$ and $s.2$. `hθgal`: $\theta$ commutes with the action of `arithmeticGalois` of every $\sigma\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $F_M$.
--
--   *The disc laws* `hLFst` and `hLSnd`, mirror images of each other on the two sides: for strict-first places $Q\neq Q'$ with $r_1Q'=r_1Q$ an affine place, a natural number $n$ with nonzero image in $\kappa$, and $g\in R_1$.integers with nonzero residue such that $\operatorname{ord}_Qg=-n$, $\operatorname{ord}_{Q'}g=n$ and $\operatorname{ord}_Wg=0$ for every other strict-first $W$ with $r_1W=r_1Q$, if moreover $g=1+e\varepsilon$ with $e\in A$ and $\varepsilon\in R_1$.integers of nonzero residue, then $\operatorname{ord}_{r_1Q}(\bar\varepsilon_1)\ge-1$; `hLSnd` is the same statement with $R_1,r_1$, `IsStrictFst` replaced by $R_2,r_2$, `IsStrictSnd`.
--
--   *The modular-unit clause* `hUnit`: there are $u_1,u_2\in F_M$ and divisors $D_1,D_2$ on $F_M$ with $D_i(W)=\operatorname{ord}_Wu_i$ for all $W$, such that (i) $u_1$ and $u_1^{-1}$ lie in $R_1$.integers and the residue of $u_1$ is nonzero, for every place $v$ of $\bar F$ that is not `Fixed` the pushforward $(r_1)_*(\text{strict-first part of }D_1)$ at $v$ equals $\operatorname{ord}_v(\bar u_1)$, and for every $\infty$-side place $C$ the pushforward $(r_1)_*(D_1$ restricted to the $\infty$-side$)$ at $r_1C$ equals $\operatorname{ord}_{r_1C}(\bar u_1)$; (ii) every nonzero $f\in F_M$ admits $m\neq0$ in $\mathbb N$ and $j\in\mathbb Z$ with $f^{m}u_1^{\,j}\in R_2$.integers of nonzero residue; (iii) and (iv) the mirror statements for $u_2$, $R_2$, $r_2$, the strict-second part of $D_2$ and the $0$-side, together with: every nonzero $f$ admits $m\neq0$, $j$ with $f^{m}u_2^{\,j}\in R_1$.integers of nonzero residue. Here `IsInftySide` means cuspidal (no $x$ with Laurent series `jqModC` has $\operatorname{ord}_W(x-a)>0$ for $a\in A$) together with the existence of $x,x'$ with Laurent series $j(q)$, $j(q^{p})$ and of $\tau\in A$ of residue $1$ with $W$-value $\tau$ at $x'/x^{p}$, and `IsZeroSide` is the corresponding condition with the predicate `IsCuspidal'` and the function $x/x'^{p}$.
--
--   *The cusp-fibre clause* `hcusp`: every non-affine place $w$ of $\bar F$ is $r_1C$ for some $\infty$-side place $C$ and $r_2C'$ for some $0$-side place $C'$. *Orientation of cuspidal readings*: `horientInf` gives $\delta(\varphi(r_1C))=r_2C$ for $\infty$-side $C$, and `horient0` gives $r_1C=\varphi(r_2C)$ for $0$-side $C$.
--
--   *The node annuli.* $e\colon SS\to\mathbb N$ is strictly positive (`he`), and `hAnn` provides for each $s\in SS$ an `Annulus` $An$ over $A$ in $F_M$ (domain of rational places, parameter, modulus in the maximal ideal of $A$, with the axioms of the structure) such that: a place $W$ lies in $An.\mathrm{dom}$ exactly when $r_1W=s.1.1$ and $W$ is neither strict-first nor strict-second; the modulus is $p^{e(s)}$ times a unit of $A$; the parameter is fixed by `arithmeticGalois` of every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`; $(\mathrm{modulus})^{-1}\cdot\mathrm{param}$ lies in $R_1$.integers and $\mathrm{param}$ lies in $R_2$.integers with nonzero residue; the $R_2$-residue of $\mathrm{param}$ has order $1$ at $s.1.2$ and satisfies a unit principle (for $f\in R_2$.integers of nonzero residue with $\operatorname{ord}_Pf=0$ on the annulus, $P.\mathrm{evalAt}(f)\cdot P.\mathrm{evalAt}(\mathrm{param})^{-\operatorname{ord}_{s.1.2}(\bar f_2)}$ lies in $A$ and is a unit, for each $P$ in the domain); and the mirror clause on the first side for $\mathrm{modulus}\cdot\mathrm{param}^{-1}$, $R_1$ and $s.1.1$.
--
--   *Node coordinates* $W$ (a finite set of places of $\bar F$) is characterised by `hW`: $w\in W$ iff $w=s.1$ or $w=s.2$ for some $s\in SS$.
--
--   *The cusp dictionary*: `hcuspV` (a place $V$ of $F_M$ with $r_1V$ non-affine is cuspidal), `hsides` (a cuspidal place is $\infty$-side or $0$-side), `hInftyNA`, `hInftyNA'` (for $\infty$-side $V$ neither $r_1V$ nor $r_2V$ is affine) and `hZeroNA`, `hZeroNA'` (the same for $0$-side $V$). *Affineness* `hφaff`: $v\mapsto\delta(\varphi(v))$ preserves affine places.
--
--   *Zones* `hzone`: every finite set $T$ of places of $\bar F$ disjoint from $W$ is contained in a finite set $Z$, disjoint from $W$, which contains $\delta(\varphi(v))$ and $\varphi(v)$ for $v\in T$, contains every $v$ with $\delta(\varphi(v))\in T$ or $\varphi(v)\in T$, contains every non-affine place, and contains every `Fixed` place outside $W$.
--
--   *Auxiliary strict places* `hAUX`: for every finite set $B$ of places of $\bar F$ and all $m_1,m_2\in\mathbb N$ there are families $Q_1\colon\mathrm{Fin}\,m_1\to$ places of $F_M$ and $Q_2\colon\mathrm{Fin}\,m_2\to$ places of $F_M$ with all $Q_1i$ strict-first, all $Q_2j$ strict-second, $i\mapsto r_1(Q_1i)$ and $j\mapsto r_2(Q_2j)$ injective with images avoiding $B$, and all $Q_1i$, $Q_2j$ fixed by `arithmeticGalois` of every element of `A.inertiaSubgroupIn ℚ`.
--
--   *Interpolation on the fibre* `hINTERP`: for finite sets $U,Z_v,Z_a$ of places of $\bar F$, a place $t_0$, $b\in\kappa$, a prescribed value function $\mathrm{val}$ and a finite set $\mathrm{bad}\subset\kappa$, if $U,Z_v,Z_a$ are pairwise disjoint, $t_0$ lies in none of them and $\#Z_v+2\,\mathrm{genus}(\bar F/\kappa)+2\le\#U$, then some $g$ in the Riemann–Roch space of $\sum_{u\in U}u$ satisfies $\operatorname{ord}_{t_0}(g-b)=1$, takes the value $\mathrm{val}(z)$ at each $z\in Z_v$, and at each $z\in Z_a$ takes some value outside $\mathrm{bad}$.
--
--   *Realisation* `hREAL`: for every set $S$ of automorphisms of $\overline{\mathbb Q}$ over $\mathbb Q$ contained in `A.inertiaSubgroupIn ℚ`, every effective divisor $D$ on $F_M$ whose support consists of strict-first and strict-second places (`IsGoodDiv`) and is fixed pointwise by $S$, such that $\deg (r_1)_*(\text{strict-first part of }D)\ge 2g-1+\#SS$ and $\deg (r_2)_*(\text{strict-second part of }D)\ge 2g-1$ with $g=\mathrm{genus}(\bar F/\kappa)$, and for every $g_1,g_2$ in the Riemann–Roch spaces of those two pushforwards taking, at each $s\in SS$, a common value at $s.1$ and $s.2$, there exists $G\in F_M$ lying in both rings of integers, in the Riemann–Roch space of $D$, with $R_1$-residue $g_1$ and $R_2$-residue $g_2$, and fixed by every $\sigma\in S$.
--
--   *The target*: $T$ is a finite set of places of $\bar F$ disjoint from $W$ (`hT`), and $V_0$ is a place of $F_M$ with $r_1V_0\in T$ or $r_2V_0\in T$ (`hV₀`).
--
--   **The conclusion.** There exist a finite set $Z$ of places of $\bar F$, an element $f\in F_M$ lying in $R_1$.integers and in $R_2$.integers, and a divisor $D$ on $F_M$ such that:
--
--   1. $Z$ contains $T$, contains every non-affine place of $\bar F$, contains every `Fixed` place outside $W$, and is disjoint from $W$;
--
--   2. $f\neq0$ and both residues $\bar f_1=R_1.\mathrm{residue}(f)$ and $\bar f_2=R_2.\mathrm{residue}(f)$ are nonzero;
--
--   3. $D(V)=\operatorname{ord}_Vf$ for every place $V$ of $F_M$, and $D(V_0)=1$;
--
--   4. every $V$ with $D(V)<0$ is strict-first with $r_1V\notin Z$, or strict-second with $r_2V\notin Z$;
--
--   5. $\operatorname{ord}_z(\bar f_1)=0$ for every $z\in Z\cup W$ with $z\neq r_1V_0$, and $\operatorname{ord}_z(\bar f_2)=0$ for every $z\in Z\cup W$ with $z\neq r_2V_0$;
--
--   6. either $\operatorname{ord}_{r_1V_0}(\bar f_1)=1$ and $\operatorname{ord}_{r_2V_0}(\bar f_2)=0$, or $\operatorname{ord}_{r_1V_0}(\bar f_1)=0$ and $\operatorname{ord}_{r_2V_0}(\bar f_2)=1$;
--
--   7. no place $V\neq V_0$ with $D(V)\ge1$ has both $r_1V\in Z$ and $r_2V\in Z$;
--
--   8. every $V$ in the support of $D$ other than $V_0$ has $r_1V\notin T$ and $r_2V\notin T$;
--
--   9. every $\sigma\in$ `A.inertiaSubgroupIn ℚ` whose `arithmeticGalois` action fixes $V_0$ also fixes $f$.
--
--   This is the main construction step in the mod-$p$ analysis of $X_H(M)$ at a prime exactly dividing the level: from the place-specialization and prolongation package on the two degeneracy readings it produces a function on $X_H(M)$ whose divisor has a simple zero at a prescribed place $V_0$, whose two residues on the fibre curve have completely prescribed order tables on the zone $Z$ and on the node coordinates $W$, and which is invariant under the inertia stabiliser of $V_0$. It is used by [`ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq`](thm.html#ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq), the form of the one-point mover in which the auxiliary orientation and order data have been discharged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_ord_eq_one_orderTables_of_realisation_forall_inertia_smul_eq.lean

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

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_ord_eq_one_orderTables_of_realisation_forall_inertia_smul_eq
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

    (W : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) (hW : ∀ w, w ∈ W ↔ ∃ s ∈ SS, w = s.1 ∨ w = s.2)

    (hcuspV : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V) → JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V)
    (hsides : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V → JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) V ∨ JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V)
    (hInftyNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) V → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V))
    (hInftyNA' : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) V → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V))
    (hZeroNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V))
    (hZeroNA' : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V))

    (hφaff : ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v)))

    (hzone : ∀ T : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (∀ t ∈ T, t ∉ W) →
      ∃ Z : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), (∀ v ∈ T, v ∈ Z) ∧
        (∀ v ∈ T, δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v) ∈ Z) ∧ (∀ v, δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v) ∈ T → v ∈ Z) ∧
        (∀ v ∈ T, qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v ∈ Z) ∧ (∀ v, qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v ∈ T → v ∈ Z) ∧
        (∀ v, ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → v ∈ Z) ∧ (∀ v, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → v ∉ W → v ∈ Z) ∧
        (∀ v ∈ Z, v ∉ W))

    (hAUX : ∀ (B : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) (m₁ m₂ : ℕ),
      ∃ (Q₁ : Fin m₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂ : Fin m₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
        (∀ i, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (Q₁ i)) ∧ (∀ j, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ (Q₂ j)) ∧
        (Function.Injective fun i => Psp.reduceFst α hα (Q₁ i)) ∧ (Function.Injective fun j => Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (Q₂ j)) ∧
        (∀ i, Psp.reduceFst α hα (Q₁ i) ∉ B) ∧ (∀ j, Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (Q₂ j) ∉ B) ∧
        (∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₁ i = Q₁ i) ∧
        (∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₂ j = Q₂ j))

    (hINTERP : ∀ (U Zv Za : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) (t₀ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (b : ResidueField ↥A) (val : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → ResidueField ↥A) (bad : Finset (ResidueField ↥A)),
      Disjoint U Zv → Disjoint U Za → Disjoint Zv Za → t₀ ∉ U → t₀ ∉ Zv → t₀ ∉ Za →
      Zv.card + 2 * genusFF (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) + 2 ≤ U.card →
      ∃ g : (Fbar p M H hpM (ResidueField ↥A)), g ∈ riemannRochSpace (∑ u ∈ U, Finsupp.single u (1 : ℤ)) ∧
        t₀.ord (g - algebraMap (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) b) = 1 ∧ (∀ z ∈ Zv, z.HasValue g (val z)) ∧
        (∀ z ∈ Za, ∃ γ : ResidueField ↥A, γ ∉ bad ∧ z.HasValue g γ))

    (hREAL : ∀ (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), (∀ σ ∈ S, σ ∈ A.inertiaSubgroupIn ℚ) →
      ∀ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), 0 ≤ D → Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ D →
      (∀ V ∈ D.support, ∀ σ ∈ S, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) →
      2 * (genusFF (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) : ℤ) - 1 + SS.card ≤ (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D)).degree →
      2 * (genusFF (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) : ℤ) - 1 ≤ (Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D)).degree →
      ∀ (g₁ g₂ : (Fbar p M H hpM (ResidueField ↥A))),
        g₁ ∈ riemannRochSpace (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D)) →
        g₂ ∈ riemannRochSpace (Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D)) →
        (∀ s ∈ SS, ∃ c : ResidueField ↥A, s.1.HasValue g₁ c ∧ s.2.HasValue g₂ c) →
        ∃ (G : ↥(xHFunctionFieldBar M H)) (h₁ : G ∈ Rpd.R₁.integers) (h₂ : G ∈ Rpd.R₂.integers),
          G ∈ riemannRochSpace D ∧ Rpd.R₁.residue ⟨G, h₁⟩ = g₁ ∧ Rpd.R₂.residue ⟨G, h₂⟩ = g₂ ∧
          ∀ σ ∈ S, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • G = G)
    (T : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) (hT : ∀ t ∈ T, t ∉ W)
    (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV₀ : Psp.reduceFst α hα V₀ ∈ T ∨ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V₀ ∈ T) :
    ∃ (Z : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      ((∀ v ∈ T, v ∈ Z) ∧ (∀ v, ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → v ∈ Z) ∧
        (∀ v, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → v ∉ W → v ∈ Z) ∧ (∀ v ∈ Z, v ∉ W)) ∧
      f ≠ 0 ∧ Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 ∧
      (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
      (∀ V, D V < 0 → (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∧ Psp.reduceFst α hα V ∉ Z) ∨ (Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V ∉ Z)) ∧
      (∀ z, (z ∈ Z ∨ z ∈ W) → z ≠ Psp.reduceFst α hα V₀ → z.ord (Rpd.R₁.residue ⟨f, h₁⟩ : (Fbar p M H hpM (ResidueField ↥A))) = 0) ∧
      (∀ z, (z ∈ Z ∨ z ∈ W) → z ≠ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V₀ → z.ord (Rpd.R₂.residue ⟨f, h₂⟩ : (Fbar p M H hpM (ResidueField ↥A))) = 0) ∧
      (((Psp.reduceFst α hα V₀).ord (Rpd.R₁.residue ⟨f, h₁⟩ : (Fbar p M H hpM (ResidueField ↥A))) = 1 ∧ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V₀).ord (Rpd.R₂.residue ⟨f, h₂⟩ : (Fbar p M H hpM (ResidueField ↥A))) = 0) ∨
        ((Psp.reduceFst α hα V₀).ord (Rpd.R₁.residue ⟨f, h₁⟩ : (Fbar p M H hpM (ResidueField ↥A))) = 0 ∧ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V₀).ord (Rpd.R₂.residue ⟨f, h₂⟩ : (Fbar p M H hpM (ResidueField ↥A))) = 1)) ∧
      (∀ V, V ≠ V₀ → 1 ≤ D V → Psp.reduceFst α hα V ∈ Z → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V ∈ Z → False) ∧
      (∀ V ∈ D.support, V ≠ V₀ → Psp.reduceFst α hα V ∉ T ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V ∉ T) ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V₀ = V₀ → (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • f = f := by sorry
