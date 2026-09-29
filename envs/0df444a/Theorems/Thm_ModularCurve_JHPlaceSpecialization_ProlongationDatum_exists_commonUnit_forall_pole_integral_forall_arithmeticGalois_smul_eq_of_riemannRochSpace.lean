-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_forall_pole_integral_forall_arithmeticGalois_smul_eq_of_riemannRochSpace
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_forall_pole_integral_forall_arithmeticGalois_smul_eq_of_riemannRochSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/96af9724-bea0-538d-b449-f745b15d6957
-- title:
--   S-invariant common unit moving L(D)-poles to integral j
-- statement:
--   **Setting.** Let $p$ be a prime and $M$ a non-zero natural number with $p \mid M$ and $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup; the hypothesis `hHp` requires that every unit of $\mathbb{Z}/M$ mapping to $1$ in $(\mathbb{Z}/(M/p))^\times$ lies in $H$, and $M/p$ is non-zero. Write $F =$ `xHFunctionFieldBar M H` for the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of $X_H(M)$, and $F' =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with the subgroup `infSubgroup p M H hpM`, the image of $H$ in $(\mathbb{Z}/(M/p))^\times$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA`, i.e. `A.LiesOverPrime p`), whose residue field $\kappa$ is algebraically closed of characteristic $p$, and write $\bar F =$ `Fbar p M H hpM κ` for the $\kappa$-function field of $q$-expansions at the level group `ΓN p M H hpM`.
--
--   **Degeneracies and the transported automorphism.** Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of $F$ and $\alpha : F' \to F$ an $\overline{\mathbb{Q}}$-algebra homomorphism, with $\alpha$ integral (`hα`) and $\theta \circ \alpha$ integral (`hβ`). The hypothesis `hα_coe` says that $\alpha$ leaves $q$-expansions unchanged, and `hβ_coe` says that the $q$-expansion of $(\theta\circ\alpha)(u)$ is `qExpand (AlgebraicClosure ℚ) p` applied to that of $u$, i.e. $u(q)\mapsto u(q^p)$. By `hθgal`, $\theta$ commutes with the action of every $\sigma \in \mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ through `arithmeticGalois (xHFunctionField M H)` (the coefficientwise semilinear action on $q$-expansions).
--
--   **The diamond map on places.** Let `pb` be a unit of $\mathbb{Z}/(M/p)$ whose underlying element is $p$ (`hpb`), and let $\delta$ be a self-map of the set of places of $\bar F$ over $\kappa$; `hδ` requires that $\delta v$ is the translate of $v$ under the semilinear automorphism `SemilinearAut.ofAlgAut` attached to the diamond automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)`.
--
--   **Nodes.** Let `SS` be a finite set of pairs of places of $\bar F$ whose members are, by `hSS`, exactly the elements of `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is the pairs $s$ with $s.2$ a supersingular place (in `ssPlacesQExp`) and $s.1 =$ `qExpFrobeniusPlaceModL κ (ΓN …) p` applied to $s.2$.
--
--   **Specialisation and prolongation data.** Let `Psp` be a `JHPlaceSpecialization p M H hpM A`: a map `sp` from places of $F'$ over $\overline{\mathbb{Q}}$ to places of $\bar F$ over $\kappa$ together with a homomorphism on degree-zero Picard groups, subject to the structure's axioms (compatibility of push-forward of principal divisors with reduction of $q$-expansions, surjectivity of `sp`, existence of reductions of principal divisors, invariance under the inertia subgroup of $A$ over $\mathbb{Q}$, Frobenius equivariance, and compatibility of the Picard map with push-forward). For a place $W$ of $F$ one writes $\mathrm{red}_1 W =$ `Psp.reduceFst α hα W` $=$ `sp` of the restriction of $W$ along $\alpha$, and $\mathrm{red}_2 W =$ `Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W` $= \delta($`sp` of the restriction of $W$ along $\theta\circ\alpha)$; $W$ is *strict first* when $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$ and $\mathrm{red}_1 W$ is not $\delta$-fixed, and *strict second* when $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ and $\mathrm{red}_2 W$ is not $\delta$-fixed, where $\mathrm{Frob} =$ `qExpFrobeniusPlaceModL κ (ΓN …) p` and a place $v$ of $\bar F$ is $\delta$-*fixed* when $\mathrm{Frob}(\delta(\mathrm{Frob}(v))) = v$. Let `Rpd` be a `JHPlaceSpecialization.ProlongationDatum Psp θ`: two regular prolongations $R_1, R_2$ of $A$ to $F$ with residue maps onto $\bar F$, such that the $R_1$-residue of a $q$-expansion with coefficients in $A$ is its coefficientwise reduction, and $f \in R_2$ if and only if $\theta f \in R_1$, with the $R_2$-residue of $f$ equal to the $R_1$-residue of $\theta f$.
--
--   **Laws imposed on the data.** `hFix`: for every supersingular place $y$, both $y$ and $\mathrm{Frob}(y)$ are $\delta$-fixed. `hFixFin`: the set of $\delta$-fixed places of $\bar F$ is finite. `hTD` (`TypeDichotomy`): every place $W$ of $F$ satisfies $\mathrm{red}_1 W = \mathrm{Frob}(\mathrm{red}_2 W)$ or $\delta(\mathrm{Frob}(\mathrm{red}_1 W)) = \mathrm{red}_2 W$. `hmodel` (`IsModel`): the conjunction of the four laws `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty` and `CuspLawZero` of the prolongation datum. `hO` (`OrderLawFixed`): for $f$ lying in both $R_1$ and $R_2$ with non-zero residues, and $D_f$ the divisor of $f$, for every $\delta$-fixed place $v$ of $\bar F$ which is an affine place (`IsAffinePlace`: $j$ takes a value in $\kappa$ at $v$), the push-forward $\mathrm{red}_{1*}D_f$ at $v$ equals $\mathrm{ord}_v$ of the $R_1$-residue of $f$ plus $\mathrm{ord}_{\delta(\mathrm{Frob}\,v)}$ of its $R_2$-residue. `hreg` (`RegularityLaw` for `SS`): two clauses, stating for $f$ in both prolongations that non-negativity of $\mathrm{ord}_V f$ over all $V$ above a $\delta$-fixed affine place $v$ forces non-negativity of the orders of the two residues at $v$ and at $\delta(\mathrm{Frob}\,v)$, and that non-negativity over all $V$ above $s.1$ forces the two residues to take a common value at $s.1$ and $s.2$ for $s \in$ `SS`. `hnv` (`NodeValueLaw` for `SS`): for $f$ in both prolongations with non-zero residues and $s \in$ `SS`, if no place $V$ with $\mathrm{ord}_V f \ne 0$ has $(\mathrm{red}_1 V, \mathrm{red}_2 V) = s$, then the two residues take one and the same non-zero value $c \in \kappa$ at $s.1$ and at $s.2$.
--
--   **Local bounds at paired poles.** The hypotheses `hLFst` and `hLSnd` are mirror statements for the two prolongations. `hLFst`: for all strict-first places $Q \ne Q'$ of $F$ with $\mathrm{red}_1 Q' = \mathrm{red}_1 Q$ an affine place, every $n \in \mathbb{N}$ with $n \ne 0$ in $\kappa$, every $g \in R_1$ with non-zero $R_1$-residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict-first $W$ with $\mathrm{red}_1 W = \mathrm{red}_1 Q$, and all $e \in A$ and $\varepsilon \in R_1$ with non-zero $R_1$-residue such that $g = 1 + e\varepsilon$ (the image of $e$ in $F$ times $\varepsilon$): then $-1 \le \mathrm{ord}_{\mathrm{red}_1 Q}$ of the $R_1$-residue of $\varepsilon$. `hLSnd` is the same with $R_2$, strict-second places and $\mathrm{red}_2$ throughout.
--
--   **Existence of comparison units.** `hUnit` asserts the existence of $u_1, u_2 \in F$ and divisors $D_1, D_2$ of $F$ with $D_i(W) = \mathrm{ord}_W u_i$ for all $W$, such that: $u_1$ and $u_1^{-1}$ lie in $R_1$ and the $R_1$-residue of $u_1$ is non-zero; the push-forward under $\mathrm{red}_1$ of the strict-first part of $D_1$ agrees at every place $v$ of $\bar F$ that is not $\delta$-fixed with $\mathrm{ord}_v$ of that residue; the push-forward under $\mathrm{red}_1$ of the restriction of $D_1$ to the places satisfying `IsInftySide` agrees at $\mathrm{red}_1 C$, for every $C$ satisfying `IsInftySide`, with $\mathrm{ord}_{\mathrm{red}_1 C}$ of that residue; and every non-zero $f \in F$ admits $m \ne 0$ in $\mathbb{N}$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j} \in R_2$ of non-zero $R_2$-residue. Symmetrically, $u_2$ and $u_2^{-1}$ lie in $R_2$ with non-zero $R_2$-residue, the corresponding two identities hold for the strict-second part of $D_2$ and for the restriction of $D_2$ to the places satisfying `IsZeroSide`, with $\mathrm{red}_2$ in place of $\mathrm{red}_1$, and every non-zero $f \in F$ admits $m \ne 0$ and $j \in \mathbb{Z}$ with $f^m u_2^{\,j} \in R_1$ of non-zero $R_1$-residue. Here `IsInftySide C` means that $C$ is cuspidal and $x'/x^p$ has at $C$ a value in $A$ with residue $1$, where $x$, $x'$ have $q$-expansions $j(q)$ and $j(q^p)$; `IsZeroSide C` is the analogous condition for $x/x'^{\,p}$ with the cuspidality condition `IsCuspidal'`.
--
--   **Cusps and orientation.** `hcusp`: every place $w$ of $\bar F$ which is not an affine place is both the $\mathrm{red}_1$-image of some place satisfying `IsInftySide` and the $\mathrm{red}_2$-image of some place satisfying `IsZeroSide`. `horientInf`: $\delta(\mathrm{Frob}(\mathrm{red}_1 C)) = \mathrm{red}_2 C$ for every $C$ satisfying `IsInftySide`. `horient0`: $\mathrm{red}_1 C = \mathrm{Frob}(\mathrm{red}_2 C)$ for every $C$ satisfying `IsZeroSide`.
--
--   **Annuli at the nodes.** Let $e :$ `SS` $\to \mathbb{N}$ with $e(s) > 0$ for all $s$ (`he`). The hypothesis `hAnn` requires for each $s \in$ `SS` an [`AlgebraicCurve.Annulus A F`](def/AlgebraicCurve_SemistableCharts.html#L86) with domain `An.dom`, parameter $t =$ `An.param` and modulus $\pi =$ `An.modulus` $\in \mathfrak{m}_A$, such that: a place $W$ of $F$ lies in `An.dom` precisely when $\mathrm{red}_1 W = s.1$ and $W$ is neither strict first nor strict second; $\pi = p^{e(s)}u$ for some unit $u$ of $A$; $t$ is fixed by the arithmetic Galois action of every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`; $\pi^{-1}t \in R_1$; $t \in R_2$ with non-zero $R_2$-residue; $t \in R_2$ with $\mathrm{ord}_{s.2}$ of its $R_2$-residue equal to $1$, and for every $f \in R_2$ with non-zero $R_2$-residue and $\mathrm{ord}_P f = 0$ for all $P \in$ `An.dom`, and every such $P$, the element $P.\mathrm{evalAt}(f)\cdot P.\mathrm{evalAt}(t)^{-n}$ with $n = \mathrm{ord}_{s.2}$ of the $R_2$-residue of $f$ lies in $A$ and is a unit of $A$; and, mirroring this, $\pi t^{-1} \in R_1$ with $\mathrm{ord}_{s.1}$ of its $R_1$-residue equal to $1$, and for every $f \in R_1$ with non-zero $R_1$-residue and $\mathrm{ord}_P f = 0$ on `An.dom`, and every $P \in$ `An.dom`, the element $P.\mathrm{evalAt}(f)\cdot P.\mathrm{evalAt}(\pi t^{-1})^{-n'}$ with $n' = \mathrm{ord}_{s.1}$ of the $R_1$-residue of $f$ lies in $A$ and is a unit of $A$.
--
--   **The divisor and the symmetry group.** Let $S$ be a set of automorphisms of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$, all lying in `A.inertiaSubgroupIn ℚ` (`hS`). Let $D$ be a divisor of $F$ with $0 \le D$ (`hD`), every place in its support strict first or strict second (`hgood`, `IsGoodDiv`), and every place in its support fixed by the arithmetic Galois action of every $\sigma \in S$ (`hDfix`). Let $x \in F$ have $q$-expansion `jqModC (AlgebraicClosure ℚ)`, the $q$-expansion of $j$ (`hx`). Finally, the Riemann–Roch space `riemannRochSpace D` $= \{f \in F : v(f) \le \exp(D v)$ for all places $v\}$ is assumed finite-dimensional over $\overline{\mathbb{Q}}$.
--
--   **Conclusion.** Under these hypotheses there exists $U \in F$ such that:
--
--   1. $U$ lies in the valuation subring $R_1$ and is a unit there;
--
--   2. $U$ lies in the valuation subring $R_2$ and is a unit there;
--
--   3. $\sigma \cdot U = U$ for every $\sigma \in S$, the action being that of `arithmeticGalois (xHFunctionField M H)`;
--
--   4. for every non-zero $f \in$ `riemannRochSpace D` and every place $W$ of $F$ over $\overline{\mathbb{Q}}$ with $\mathrm{ord}_W(Uf) < 0$ there exists $a \in A$ with $0 < \mathrm{ord}_W\bigl(x - a\bigr)$, the image of $a$ in $F$ being understood;
--
--   5. for every non-zero $f \in$ `riemannRochSpace D` and every place $W$ of $F$ with $\mathrm{ord}_W(Uf) < 0$ there exists $a \in A$ with $0 < \mathrm{ord}_W\bigl(\theta^{-1}x - a\bigr)$.
--
--   This is the normalisation step which, after multiplication by a single unit $U$ of both prolongations invariant under the prescribed inertia automorphisms, confines the poles of all functions in $L(D)$ to places at which both $j$ and its $\theta$-transform take values integral over $A$ — in particular away from the cusps — in the analysis of the semistable reduction of the Jacobian of $X_H(M)$ at a prime $p$ exactly dividing $M$. It is used by [`ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_unit_smul_riemannRochSpace_basis_coeffMap_eq_smul_forall_arithmeticGalois_smul_eq`](thm.html#ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_unit_smul_riemannRochSpace_basis_coeffMap_eq_smul_forall_arithmeticGalois_smul_eq), where such a $U$ is applied to a basis of $L(D)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_forall_pole_integral_forall_arithmeticGalois_smul_eq_of_riemannRochSpace.lean

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
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_forall_pole_integral_forall_arithmeticGalois_smul_eq_of_riemannRochSpace
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
    (x : ↥(xHFunctionFieldBar M H)) (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace D)] :
    ∃ U : ↥(xHFunctionFieldBar M H),
      (∃ h₁ : U ∈ Rpd.R₁.integers, IsUnit (⟨U, h₁⟩ : Rpd.R₁.integers)) ∧
      (∃ h₂ : U ∈ Rpd.R₂.integers, IsUnit (⟨U, h₂⟩ : Rpd.R₂.integers)) ∧
      (∀ σ ∈ S, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • U = U) ∧
      (∀ f ∈ riemannRochSpace D, f ≠ 0 → ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.ord (U * f) < 0 →
        ∃ a : ↥A, 0 < W.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))) ∧
      (∀ f ∈ riemannRochSpace D, f ≠ 0 → ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.ord (U * f) < 0 →
        ∃ a : ↥A, 0 < W.ord (θ.symm x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))) := by sorry
