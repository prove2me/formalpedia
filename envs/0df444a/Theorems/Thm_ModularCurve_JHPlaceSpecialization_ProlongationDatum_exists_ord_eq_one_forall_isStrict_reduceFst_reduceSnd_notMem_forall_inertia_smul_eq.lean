-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/3c48e725-6115-5e52-8320-72ea97ef6303
-- title:
--   Inertia-equivariant function with prescribed simple zero on X_H(M)
-- statement:
--   Throughout, $p$ is a prime and $M$ a non-zero natural number with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and $H \le (\mathbb{Z}/M)^\times$ is a subgroup containing every unit whose image under `ZMod.unitsMap` in $(\mathbb{Z}/(M/p))^\times$ is trivial (`hHp`); $H' =$ `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb{Z}/(M/p))^\times$. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ in which $p$ is a non-unit (`hA`, i.e. `A.LiesOverPrime p`), whose residue field $\kappa$ is algebraically closed of characteristic $p$. Write $F =$ `xHFunctionFieldBar M H` and $F' =$ `xHFunctionFieldBar (M/p) H'` for the base changes to $\overline{\mathbb{Q}}$ of the $q$-expansion function fields of $X_H(M)$ and $X_{H'}(M/p)$ inside $\overline{\mathbb{Q}}((q))$, and $\bar F =$ `Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ of `ΓN p M H hpM`. A place of a field extension is a proper valuation subring containing the base field which is a principal ideal ring, `ord` is its associated additive valuation, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Let $\Phi =$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` denote the operation on places of $\bar F$ given by restriction along the mod-$p$ Frobenius of $\bar F$.
--
--   The data are: an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F$; an $\overline{\mathbb{Q}}$-algebra map $\alpha : F' \to F$, integral (`hα`), with $\theta \circ \alpha$ integral (`hβ`), such that $\alpha$ preserves $q$-expansions (`hα_coe`) while $\theta \circ \alpha$ replaces $q$ by $q^p$, i.e. composes the $q$-expansion with `qExpand _ p` (`hβ_coe`), and such that $\theta$ commutes with the arithmetic Galois action `arithmeticGalois` of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F$ (`hθgal`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`); a map $\delta$ on places of $\bar F$ which is the action of the semilinear automorphism attached to the diamond operator `diamondActionModL κ (M/p) H' (CuspForm.gammaLift (M/p) pb)` (`hδ`); a finite set $SS$ of pairs of places of $\bar F$ whose members are exactly the pairs $(\Phi(v), v)$ with $v$ supersingular, i.e. `ssNodePairsQExp κ (ΓN p M H hpM) p` (`hSS`); a place specialization $Psp$ of type `JHPlaceSpecialization p M H hpM A` (a surjective map `sp` from places of $F'$ to places of $\bar F$, compatible with divisors of functions and their reductions, inertia-invariant, and turning Frobenius elements into $\Phi$, together with a compatible map on degree-zero divisor classes); and a prolongation datum $Rpd$ of type `ProlongationDatum Psp θ`, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F$ with residue field $\bar F$, such that $R_1$-integrality and residues are computed from $q$-expansions with coefficients in $A$, and $f \in R_2$ iff $\theta f \in R_1$, with $R_2$-residue of $f$ equal to the $R_1$-residue of $\theta f$. For a place $W$ of $F$ set $r_1(W) =$ `Psp.reduceFst α hα W` $= \mathrm{sp}(W|_\alpha)$ and $r_2(W) =$ `Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W` $= \delta(\mathrm{sp}(W|_{\theta\circ\alpha}))$; $W$ is strict of the first kind when $\delta(\Phi(r_1(W))) = r_2(W)$ and $r_1(W)$ is not $\delta$-fixed, and strict of the second kind when $r_1(W) = \Phi(r_2(W))$ and $r_2(W)$ is not $\delta$-fixed, where a place $v$ of $\bar F$ is $\delta$-fixed (`Fixed`) when $\Phi(\delta(\Phi(v))) = v$; $v$ is an affine place when the $j$-function on $\bar F$ has a value in $\kappa$ at $v$.
--
--   The hypotheses fall into the following groups.
--
--   Fixing and dichotomy (`hFix`, `hTD`, `hFixFin`): every supersingular place $y$ of $\bar F$ and its image $\Phi(y)$ are $\delta$-fixed; for every place $W$ of $F$ either $r_1(W) = \Phi(r_2(W))$ or $\delta(\Phi(r_1(W))) = r_2(W)$; and the set of $\delta$-fixed places of $\bar F$ is finite.
--
--   The law block (`hmodel`, `hO`, `hreg`, `hnv`, summarised here) for $\alpha$, $\theta \circ \alpha$ and $\delta$: `hmodel` asserts the two divisor laws (for $f$ integral for both prolongations with non-zero residues, the push-forward along $r_1$ of the strict-first part of $\mathrm{div}(f)$ computes the order of the $R_1$-residue at each place which is not $\delta$-fixed, and symmetrically for $r_2$, the strict-second part and the $R_2$-residue) together with the two cusp laws; `hO` is the order law at $\delta$-fixed affine places (the total push-forward along $r_1$ of $\mathrm{div}(f)$ at such a place $v$ is the order of the $R_1$-residue at $v$ plus the order of the $R_2$-residue at $\delta(\Phi(v))$); `hreg` is the regularity law relative to $SS$ (non-negativity of residue orders, and existence of common values at node pairs, under non-negativity of $\mathrm{ord}_V f$ above the place concerned); `hnv` is the node value law relative to $SS$ (if no place of $F$ with $\mathrm{ord}_V f \ne 0$ reduces to a given node pair, the two residues take a common non-zero value at its two coordinates).
--
--   Local bounds at pairs of strict places (`hLFst`, `hLSnd`): for all places $Q \ne Q'$ of $F$ which are strict of the first kind with $r_1(Q') = r_1(Q)$ and $r_1(Q)$ an affine place, for every natural number $n$ non-zero in $\kappa$, for every $g \in R_1$ with non-zero $R_1$-residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict-first place $W$ with $r_1(W) = r_1(Q)$, and for all $e \in A$ and $\varepsilon \in R_1$ with non-zero $R_1$-residue such that $g = 1 + e\varepsilon$ (the image of $e$ in $F$), the order of the $R_1$-residue of $\varepsilon$ at $r_1(Q)$ is at least $-1$; `hLSnd` is the same statement with first replaced by second throughout ($r_2$, $R_2$, strict of the second kind).
--
--   Uniformizing units (`hUnit`): there exist $u_1, u_2 \in F$ and divisors $D_1, D_2$ with $D_i = \mathrm{div}(u_i)$, such that $u_1$ and $u_1^{-1}$ lie in $R_1$ with non-zero $R_1$-residue, the push-forward along $r_1$ of the strict-first part of $D_1$ agrees at every non-$\delta$-fixed place $v$ with the order of the $R_1$-residue of $u_1$ at $v$, and the push-forward along $r_1$ of the part of $D_1$ supported on `IsInftySide` places agrees at $r_1(C)$, for every `IsInftySide` place $C$, with the order of that residue at $r_1(C)$; every non-zero $f \in F$ admits $m \ne 0$ and $j \in \mathbb{Z}$ with $f^m u_1^{\,j} \in R_2$ of non-zero $R_2$-residue; and the mirror-image conditions hold for $u_2$ with $R_2$, $r_2$, the strict-second part of $D_2$ and `IsZeroSide` places, every non-zero $f$ admitting $m \ne 0$, $j$ with $f^m u_2^{\,j} \in R_1$ of non-zero $R_1$-residue. Here `IsInftySide` means cuspidal for the $j$-function together with a unit-value condition on $x'/x^p$, and `IsZeroSide` means cuspidal for $j$ composed with `qExpand _ p` together with the analogous condition on $x/x'^p$.
--
--   Cusps and orientation (`hcusp`, `horientInf`, `horient0`): every non-affine place $w$ of $\bar F$ is $r_1(C)$ for some `IsInftySide` place $C$ and $r_2(C')$ for some `IsZeroSide` place $C'$; $\delta(\Phi(r_1(C))) = r_2(C)$ for every `IsInftySide` place $C$; and $r_1(C) = \Phi(r_2(C))$ for every `IsZeroSide` place $C$.
--
--   Node annuli (`e`, `he`, `hAnn`): a function $e$ on $SS$ with $e(s) > 0$, and for each $s = (s_1, s_2) \in SS$ an annulus $An$ over $A$ in $F$ whose domain consists exactly of the places $W$ with $r_1(W) = s_1$ that are neither strict of the first nor strict of the second kind; whose modulus is $p^{e(s)}$ times a unit of $A$; whose parameter is fixed by `arithmeticGalois` applied to every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ`; such that $(\mathrm{modulus})^{-1}\cdot \mathrm{param} \in R_1$; such that $\mathrm{param} \in R_2$ with non-zero $R_2$-residue, the order of that residue at $s_2$ being $1$, and such that for every $f \in R_2$ with non-zero residue and $\mathrm{ord}_P f = 0$ for all $P$ in the domain, and every such $P$, the element $P(f)\cdot P(\mathrm{param})^{-\mathrm{ord}_{s_2}(\text{residue of } f)}$ lies in $A$ and is a unit there; and symmetrically $\mathrm{modulus}\cdot \mathrm{param}^{-1} \in R_1$, the order of its $R_1$-residue at $s_1$ is $1$, and the corresponding unit statement holds for $R_1$, $s_1$ and $\mathrm{modulus}\cdot\mathrm{param}^{-1}$.
--
--   Target data: a finite set $T$ of places of $\bar F$ none of whose members is the first coordinate of a node pair in $SS$ (`hT`), and a place $V_0$ of $F$ with $r_1(V_0) \in T$ or $r_2(V_0) \in T$ (`hV₀`).
--
--   Under these hypotheses there exist $f \in F$ and a divisor $D$ on the places of $F$ over $\overline{\mathbb{Q}}$ such that: $f \ne 0$; $f$ lies in the valuation subrings of both $R_1$ and $R_2$, with both residues non-zero; $D$ is the divisor of $f$, that is $D(V) = \mathrm{ord}_V f$ for every place $V$; $D(V_0) = 1$; every $V$ in the support of $D$ with $V \ne V_0$ is strict of the first kind or strict of the second kind; every $V$ in the support of $D$ with $V \ne V_0$ satisfies $r_1(V) \notin T$ and $r_2(V) \notin T$; and for every $\sigma$ in the inertia subgroup `A.inertiaSubgroupIn ℚ` whose arithmetic Galois action fixes $V_0$, the same action fixes $f$.
--
--   This is the moving lemma used in the analysis of the special fibre at a prime $p$ exactly dividing the level: it produces a function on the base-changed function field of $X_H(M)$ which is a unit for both prolongations, has a simple zero at a prescribed place $V_0$, has all its remaining zeros and poles at places strict for one of the two reductions and away from a prescribed finite set of readings, and is invariant under those inertia elements that fix $V_0$. It is applied in [`ModularCurve.JHPlaceSpecialization.exists_inertiaStable_pic0Mk_eq_support_strict_or_node_of_inertiaStable`](thm.html#ModularCurve.JHPlaceSpecialization.exists_inertiaStable_pic0Mk_eq_support_strict_or_node_of_inertiaStable), which realises inertia-stable divisor classes on the fibre by such functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.JHNeronObjectAtP
open ModularCurve
open scoped MatrixGroups

open Classical in

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq
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
    (T : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hT : ∀ t ∈ T, ∀ s ∈ SS, t ≠ s.1)
    (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hV₀ : Psp.reduceFst α hα V₀ ∈ T ∨ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V₀ ∈ T) :
    ∃ (f : ↥(xHFunctionFieldBar M H)) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      f ≠ 0 ∧
      (∃ (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0) ∧
      (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
      (∀ V ∈ D.support, V ≠ V₀ → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V) ∧
      (∀ V ∈ D.support, V ≠ V₀ → Psp.reduceFst α hα V ∉ T ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V ∉ T) ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V₀ = V₀ →
          (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • f = f := by sorry
