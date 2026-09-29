-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_rep_inertiaFixed_support_strict_or_node_of_mem_inertiaInvariants_of_annulus_of_fixReg
-- name    : ModularCurve.JHPlaceSpecialization.exists_rep_inertiaFixed_support_strict_or_node_of_mem_inertiaInvariants_of_annulus_of_fixReg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/4f5ee31b-1d4f-53c4-862f-78a092057a22
-- title:
--   Inertia-fixed representatives of inertia-invariant classes in J_H(M)
-- statement:
--   Fix a prime $p$ and a natural number $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ subject to `hHp`: every unit $u$ of $\mathbb{Z}/M$ whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$ lies in $H$ (with $M/p \neq 0$). Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with `hA : A.LiesOverPrime p`, that is, $p$ is a non-unit of $A$, whose residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. Write $FM$ for `xHFunctionFieldBar M H` (the base change to $\overline{\mathbb{Q}}$ of the Laurent-series function field of $X_H(M)$), $FMp$ for the corresponding field at level $M/p$ with the image subgroup `infSubgroup p M H hpM`, and $Fb$ for `Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ at the group `ΓN p M H hpM`; `JH M H` is $\mathrm{Pic}^0$ of $FM$ over $\overline{\mathbb{Q}}$.
--
--   The geometric data are: a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $FM$; an integral $\overline{\mathbb{Q}}$-algebra map $\alpha : FMp \to FM$ (`hα`), with $\beta = \theta \circ \alpha$ also integral (`hβ`), such that $\alpha$ is the identity on underlying Laurent series (`hα_coe`) while $\beta$ is the substitution $q \mapsto q^p$, i.e. `qExpand (AlgebraicClosure ℚ) p`, on underlying Laurent series (`hβ_coe`); a unit $pb$ of $\mathbb{Z}/(M/p)$ reducing to $p$ (`hpb`); the operator $\delta$ on places of $Fb$ over $\kappa$ given (`hδ`) by the action of the semilinear automorphism attached to `diamondActionModL` at the $\Gamma_0(M/p)$-lift of $pb$; the finite set $SS$ of places pairs characterised by `hSS` as the supersingular node pairs `ssNodePairsQExp`, so $s \in SS$ iff $s.2$ is a supersingular place of the $q$-expansion field and $s.1 = \Phi(s.2)$, where $\Phi =$ `qExpFrobeniusPlaceModL` is restriction along the mod-$p$ Frobenius of $q$-expansions; a place specialisation `Psp` of type `JHPlaceSpecialization p M H hpM A` and a prolongation datum `Rpd` for `Psp` and $\theta$, with regular prolongations $R_1, R_2$ of $A$ in $FM$ with values in $Fb$. For a place $W$ of $FM$ one writes $\mathrm{red}_1 W =$ `Psp.reduceFst α hα W` $=$ `Psp.sp` of the restriction of $W$ along $\alpha$, and $\mathrm{red}_2 W =$ `Psp.reduceSnd` $= \delta(\mathrm{Psp.sp}$ of the restriction along $\beta)$; $W$ is strict of the first kind (`IsStrictFst`) when $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not $\delta$-fixed, and strict of the second kind (`IsStrictSnd`) when $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not $\delta$-fixed; a place $v$ of $Fb$ is $\delta$-fixed (`Fixed`) when $\Phi(\delta(\Phi v)) = v$, and affine (`IsAffinePlace`) when some element of $Fb$ with Laurent series the modular $j$-expansion has a value at $v$.
--
--   The laws imposed on this frame are: `hFix`, that every supersingular place $y$ of `ssPlacesQExp` and its Frobenius image $\Phi y$ are $\delta$-fixed; `hTD`, the type dichotomy, that every place $W$ of $FM$ satisfies $\mathrm{red}_1 W = \Phi(\mathrm{red}_2 W)$ or $\delta(\Phi(\mathrm{red}_1 W)) = \mathrm{red}_2 W$; `hmodel`, that `Rpd` is a model for $\alpha, \beta, \delta$, i.e. the two divisor laws together with the two cusp laws at the infinity and zero sides; `hO`, the order law at $\delta$-fixed affine places, that for $f$ lying in both $R_1$- and $R_2$-integers with non-zero residues and $D$ the divisor of $f$, the push-forward of $D$ along $\mathrm{red}_1$ at such a place $v$ equals $v.\mathrm{ord}$ of the $R_1$-residue of $f$ plus $(\delta(\Phi v)).\mathrm{ord}$ of the $R_2$-residue; `hreg`, the regularity law at $SS$ (non-negativity of both residue orders at $\delta$-fixed affine places, and common values at node pairs); `hnv`, the node value law at $SS$ (at a pair $s$, if no place of $FM$ with $\mathrm{ord}_V f \neq 0$ reduces to $(s.1, s.2)$, the two residues take one and the same non-zero value at $s.1$ and $s.2$); `hθgal`, that $\theta$ commutes with the arithmetic Galois action of every $\sigma \in \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$; and `hFixFin`, that the set of $\delta$-fixed places of $Fb$ is finite.
--
--   Two local lower-bound hypotheses `hLFst` and `hLSnd` are imposed, mirror images of one another for the first and second readings. In the first-kind case: for all strict-first places $Q \neq Q'$ of $FM$ with $\mathrm{red}_1 Q' = \mathrm{red}_1 Q$ affine, every $n \in \mathbb{N}$ non-zero in $\kappa$, every $g \in R_1$-integers with non-zero $R_1$-residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for all further strict-first $W$ with the same first reduction, and every $e \in A$ and $\varepsilon$ in the $R_1$-integers with non-zero residue such that $g = 1 + e\varepsilon$ (with $e$ mapped into $FM$), one has $-1 \le (\mathrm{red}_1 Q).\mathrm{ord}$ of the $R_1$-residue of $\varepsilon$; `hLSnd` is the same statement with $R_2$, $\mathrm{red}_2$ and strictness of the second kind.
--
--   The hypothesis `hUnit` asks for $u_1, u_2 \in FM$ and divisors $D_1, D_2$ on $FM$ which are the divisors of $u_1$ and $u_2$ respectively, such that: $u_1$ and $u_1^{-1}$ lie in the $R_1$-integers with $R_1$-residue of $u_1$ non-zero, the push-forward along $\mathrm{red}_1$ of the strict-first part `Psp.fstDiv` of $D_1$ agrees at every non-$\delta$-fixed place $v$ of $Fb$ with $v.\mathrm{ord}$ of that residue, and the push-forward along $\mathrm{red}_1$ of the part of $D_1$ supported on infinity-side places agrees at $\mathrm{red}_1 C$, for every infinity-side $C$, with $(\mathrm{red}_1 C).\mathrm{ord}$ of that residue; every non-zero $f \in FM$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j}$ in the $R_2$-integers with non-zero $R_2$-residue; and the mirror clauses for $u_2$, with $R_2$, $\mathrm{red}_2$, `Psp.sndDiv` of $D_2$, the zero-side places, and every non-zero $f$ admitting $m \neq 0$, $j$ with $f^m u_2^{\,j}$ in the $R_1$-integers with non-zero $R_1$-residue. Here the infinity side (`IsInftySide`) and the zero side (`IsZeroSide`) are the cuspidal conditions together with the requirement that $x'/x^p$, respectively $x/x'^p$, takes a value at the place which is a lift of $1$ in $A$, for $x, x'$ with Laurent series the $j$-expansion and its $p$-fold substitute.
--
--   The cusp and orientation hypotheses are: `hcusp`, that every non-affine place $w$ of $Fb$ is of the form $\mathrm{red}_1 C$ for some infinity-side $C$ and of the form $\mathrm{red}_2 C$ for some zero-side $C$; `horientInf`, that $\delta(\Phi(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for every infinity-side $C$; and `horient0`, that $\mathrm{red}_1 C = \Phi(\mathrm{red}_2 C)$ for every zero-side $C$.
--
--   The annulus data consist of a function $e : SS \to \mathbb{N}$ with $e(s) > 0$ (`he`), together with `hAnn`: for each $s \in SS$ there is an annulus $An$ over $A$ in $FM$ (in the sense of [`AlgebraicCurve.Annulus`](def/AlgebraicCurve_SemistableCharts.html#L86), so with a domain of rational places, a parameter and a modulus in the maximal ideal of $A$, subject to the evaluation, uniqueness, order and unit axioms of that structure) whose domain is exactly the set of places $W$ with $\mathrm{red}_1 W = s.1$ and $W$ strict of neither kind; whose modulus is $p^{e(s)}$ times a unit of $A$; whose parameter is fixed by the arithmetic Galois action of every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`; such that $(\mathrm{modulus})^{-1}\cdot \mathrm{param}$ lies in the $R_1$-integers, $\mathrm{param}$ lies in the $R_2$-integers with non-zero residue, the $R_2$-residue of $\mathrm{param}$ has order $1$ at $s.2$ and, for every $f$ in the $R_2$-integers with non-zero residue and $\mathrm{ord}_P f = 0$ throughout the annulus, the product of $P.\mathrm{evalAt} f$ with $(P.\mathrm{evalAt}\,\mathrm{param})^{-\mathrm{ord}_{s.2}(\text{residue}_2 f)}$ lies in $A$ and is a unit there for every $P$ in the domain; and symmetrically $\mathrm{modulus}\cdot \mathrm{param}^{-1}$ lies in the $R_1$-integers, its $R_1$-residue has order $1$ at $s.1$, and the corresponding unit property holds with $R_1$, $s.1$ and this element in place of the parameter.
--
--   The slope hypothesis `hVSlope` states that for every family $An$ of annuli indexed by $SS$ satisfying, for each $s$, exactly the list of conditions just described, and every $k \in \mathbb{N}$ divisible by all $e(s)$, there are $f \in FM$ and $c \in \overline{\mathbb{Q}}$ with $c \cdot f$ in the $R_1$-integers such that $f \neq 0$, the $R_1$-residue of $c\cdot f$ is non-zero, every divisor $G$ which is the divisor of $f$ is a good divisor (its support consists of places strict of the first or second kind), $\mathrm{ord}_V f = 0$ for every place $V$ of $FM$ whose first reduction is $\delta$-fixed and differs from $s.1$ for all $s \in SS$, the order of the $R_1$-residue of $c\cdot f$ vanishes at every $\delta$-fixed place $v$ of $Fb$ distinct from all $s.1$, and for each $s$ there is $a \neq 0$ in $\overline{\mathbb{Q}}$ with $\mathrm{ord}_P f = 0$ and $P.\mathrm{evalAt} f \cdot a \cdot (P.\mathrm{evalAt}(An\,s).\mathrm{param})^{-(k/e(s))}$ in $A$ and a unit there, for all $P$ in the domain of $An\,s$.
--
--   Finally, four reading hypotheses are imposed. `hFixReadFst` and `hFixReadSnd`: for $g$ in the $R_1$- (resp. $R_2$-) integers with non-zero residue and $v$ a $\delta$-fixed place of $Fb$ distinct from all $s.1$ (resp. all $s.2$), if $\mathrm{ord}_V g = 0$ for every $V$ with $\mathrm{red}_1 V = v$ (resp. $\mathrm{red}_2 V = v$), then the order at $v$ of the corresponding residue of $g$ is $0$. `hFixRegFst` and `hFixRegSnd`: the same with $v$ additionally affine, the hypothesis $0 \le \mathrm{ord}_V g$ over $v$, and the conclusion $0 \le v.\mathrm{ord}$ of the corresponding residue of $g$.
--
--   Under these hypotheses the conclusion is the following. For every $x$ in `JHPlaceSpecialization.inertiaInvariants M H A`, that is, every class $x \in$ `JH M H` with $\sigma \cdot x = x$ for all $\sigma \in$ `A.inertiaSubgroupIn ℚ`, there exists a divisor $D$ of degree zero on $FM$ over $\overline{\mathbb{Q}}$ such that:
--
--   (i) every place $V$ in the support of $D$ is fixed by the arithmetic Galois action of every $\sigma \in$ `A.inertiaSubgroupIn ℚ`, and
--
--   (ii) every such $V$ is strict of the first kind, or strict of the second kind, or satisfies $\mathrm{red}_1 V = s.1$ for some $s \in SS$; and
--
--   (iii) the class of $D$ in $\mathrm{Pic}^0$ equals $x$.
--
--   This is the moving lemma, at a prime $p$ exactly dividing the level $M$, which produces for each inertia-invariant class of $J_H(M)$ a degree-zero divisor representative whose support is inertia-stable and consists only of places that are strict of one of the two kinds or lie over a first node coordinate of a supersingular node pair. Such representatives are exactly the input on which the depth and component laws of the Néron model at $p$ are read off, and the statement is used as the representative hypothesis in the construction of the component map and its kernel clause for $J_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_rep_inertiaFixed_support_strict_or_node_of_mem_inertiaInvariants_of_annulus_of_fixReg.lean

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
open Classical in

theorem ModularCurve.JHPlaceSpecialization.exists_rep_inertiaFixed_support_strict_or_node_of_mem_inertiaInvariants_of_annulus_of_fixReg
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
    ∀ x : ↥(JHPlaceSpecialization.inertiaInvariants M H A),
      ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
        (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧
          (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)) ∧
        Pic0.mk D = (x : JH M H) := by sorry
