-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_or_fixed_and_isAffinePlace_or_isStrictFst_or_isStrictSnd
-- name    : ModularCurve.JHPlaceSpecialization.isCuspidal_or_fixed_and_isAffinePlace_or_isStrictFst_or_isStrictSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/330a6b18-9773-59c3-a2e9-df581b0733f1
-- title:
--   Typology of places of X_H(M) above p with p ‖ M
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer with $p \mid M$ (`hpM`) and $p^{2} \nmid M$ (`hpM2`), and $H \le (\mathbb{Z}/M)^{\times}$ is a subgroup containing every unit whose image under `ZMod.unitsMap` along $M/p \mid M$ is $1$ (`hHp`); $M/p$ is nonzero. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, meaning that $p$ is a nonunit of $A$ (`hA`), and its residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed.
--
--   Three function fields occur. $F_M =$ `↥(xHFunctionFieldBar M H)` is the $\overline{\mathbb{Q}}$-base change, inside $\overline{\mathbb{Q}}$-Laurent series, of the $q$-expansion function field of $X_H(M)$; $F_{M/p} =$ `↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))` is the analogous field at level $M/p$ for the image $H'=$ `infSubgroup p M H hpM` of $H$ in $(\mathbb{Z}/(M/p))^{\times}$; and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` is the $q$-expansion function field over $\kappa$ for the congruence subgroup `JHNeronObjectAtP.ΓN p M H hpM`. Places are in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): valuation subrings containing the base field, different from the whole field and with principal maximal ideal, equipped with the normalised order function `ord`. Write $\Phi$ for the mod-$p$ Frobenius operation `qExpFrobeniusPlaceModL κ (JHNeronObjectAtP.ΓN p M H hpM) p` on places of $\bar F$, given by restriction along the $q\mapsto q^{p}$ map.
--
--   The data are: an automorphism $\theta$ of $F_M$ over $\overline{\mathbb{Q}}$; two integral $\overline{\mathbb{Q}}$-algebra maps $\alpha,\beta : F_{M/p} \to F_M$ (integrality being `hα`, `hβ`); a unit $pb$ of $\mathbb{Z}/(M/p)$ reducing to $p$ (`hpb`); a map $\delta$ on places of $\bar F$ which by `hδ` is the action of the semilinear automorphism `SemilinearAut.ofAlgAut` attached to the diamond automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM)` evaluated at the lift [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$ to $\Gamma_0(M/p)$; a finite set $SS$ of pairs of places of $\bar F$ which by `hSS` consists exactly of the members of `ssNodePairsQExp κ (JHNeronObjectAtP.ΓN p M H hpM) p`, i.e. the pairs $s$ with $s_2$ a supersingular place and $s_1 = \Phi(s_2)$; a specialization `Psp : JHPlaceSpecialization p M H hpM A`, whose component `sp` sends places of $F_{M/p}$ to places of $\bar F$ compatibly with divisors of $q$-expansions, surjectively, and equivariantly for inertia and Frobenius, and which also carries a map on degree-zero divisor classes; and a prolongation datum `Rpd : Psp.ProlongationDatum θ`, consisting of two regular prolongations $R_1,R_2$ of $A$ from $\overline{\mathbb{Q}}$ to $F_M$ with residues in $\bar F$, the first computing coefficientwise reduction of Laurent series and the second obtained from the first by transport along $\theta$. For a place $W$ of $F_M$ put $r_1W =$ `Psp.reduceFst α hα W` $=$ `Psp.sp (W.restrictAlong α hα)` and $r_2W =$ `Psp.reduceSnd β hβ δ W` $= \delta(\mathrm{sp}(W|_{\beta}))$. A place $v$ of $\bar F$ is *fixed* (`JHPlaceSpecialization.Fixed`) when $\Phi(\delta(\Phi v)) = v$, and *affine* (`JHPlaceSpecialization.IsAffinePlace`) when some $x \in \bar F$ with Laurent expansion `jqModC κ` has a value in $\kappa$ at $v$.
--
--   The hypotheses fall into the following groups, all of which are assumed.
--
--   *Dichotomy and finiteness.* `hTD` (`Psp.TypeDichotomy`): for every place $W$ of $F_M$, either $r_1W = \Phi(r_2W)$ or $\delta(\Phi(r_1W)) = r_2W$. `hFix`: the set of fixed places of $\bar F$ is finite.
--
--   *The laws of the model (summarised here).* `hmodel` (`Rpd.IsModel`) is the conjunction of four laws, each quantified over $f \in F_M$ lying in the integers of both $R_1$ and $R_2$ with both residues nonzero and over a divisor $D$ equal to the divisor of $f$: the pushforward under $r_1$ of the part of $D$ supported on places strict of the first kind computes, at each non-fixed place $v$, the order at $v$ of the $R_1$-residue of $f$; the mirror statement for $r_2$, the second-kind part and the $R_2$-residue; and two cusp laws doing the same for the parts of $D$ supported on infinity-side, respectively zero-side, places, evaluated at images of such places. `hO` (`Rpd.OrderLawFixed`): under the same hypotheses on $f$ and $D$, at a fixed affine place $v$ the full pushforward of $D$ under $r_1$ at $v$ equals $\operatorname{ord}_v$ of the $R_1$-residue plus $\operatorname{ord}_{\delta(\Phi v)}$ of the $R_2$-residue. `hRL` (`Rpd.RegularityLaw`, two clauses): at a fixed affine place $v$, if every place of $F_M$ with $r_1$-image $v$ has nonnegative order at $f$ then the $R_1$-residue has nonnegative order at $v$ whenever it is nonzero, and the $R_2$-residue has nonnegative order at $\delta(\Phi v)$ whenever it is nonzero; and for $s \in SS$, if every place with $r_1$-image $s_1$ has nonnegative order at $f$, then the two residues take a common value $c \in \kappa$ at $s_1$ and at $s_2$. `hNV` (`Rpd.NodeValueLaw`): for $s \in SS$, if no place $V$ with $\operatorname{ord}_V f \neq 0$ satisfies both $r_1V = s_1$ and $r_2V = s_2$, then the two residues take a common nonzero value at $s_1$ and $s_2$.
--
--   *Normalisation of $\alpha$, $\beta$ and $\theta$.* `hα_coe`: $\alpha$ is the identity on Laurent expansions. `hβ_coe`: $\beta$ acts on Laurent expansions as `qExpand κ`-style substitution $q \mapsto q^{p}$, i.e. as `qExpand (AlgebraicClosure ℚ) p`. `hθgal`: $\theta$ commutes with the arithmetic Galois action `arithmeticGalois` of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $F_M$. `hβθ`: $\beta$ is $\alpha$ followed by $\theta$.
--
--   *Two local laws at colliding places.* `hLFst`: for places $Q \neq Q'$ of $F_M$ both strict of the first kind with the same, affine, $r_1$-image, for $n \in \mathbb{N}$ with $n \neq 0$ in $\kappa$, for $g$ in the integers of $R_1$ with nonzero residue such that $\operatorname{ord}_Q g = -n$, $\operatorname{ord}_{Q'} g = n$ and $\operatorname{ord}_W g = 0$ for every further first-kind place $W$ with the same $r_1$-image, and for $e \in A$ and $\varepsilon$ in the integers of $R_1$ with nonzero residue such that $g = 1 + e\,\varepsilon$, one has $-1 \le \operatorname{ord}_{r_1Q}$ of the $R_1$-residue of $\varepsilon$. `hLSnd` is the same statement with first kind, $r_1$ and $R_1$ replaced throughout by second kind, $r_2$ and $R_2$.
--
--   *Modular units.* `hUnit`: there exist $u_1,u_2 \in F_M$ and divisors $D_1,D_2$ of $F_M$ with $D_i$ the divisor of $u_i$, such that $u_1$ and $u_1^{-1}$ lie in the integers of $R_1$ with the residue of $u_1$ nonzero, the first divisor law holds for $D_1$ at every non-fixed place and the infinity-side cusp law holds for $D_1$, both with the $R_1$-residue of $u_1$; every nonzero $f \in F_M$ admits $m \neq 0$ and $j \in \mathbb{Z}$ with $f^{m}u_1^{j}$ in the integers of $R_2$ with nonzero residue; and symmetrically for $u_2$, $D_2$, $R_2$, $r_2$, the second-kind divisor part, the zero-side cusp law, and $f^{m}u_2^{j}$ in the integers of $R_1$ with nonzero residue.
--
--   *Cusp fibres and orientation.* `hcusp`: every non-affine place $w$ of $\bar F$ is the $r_1$-image of some infinity-side place and also the $r_2$-image of some zero-side place, where infinity-side (`IsInftySide`) and zero-side (`IsZeroSide`) are the cuspidality conditions of `IsCuspidal`, respectively `IsCuspidal'`, together with the existence of a value with residue $1$ of $x'/x^{p}$, respectively $x/x'^{p}$, for $x,x'$ with expansions `jqModC` and its $q\mapsto q^{p}$ substitute. `horientInf`: $\delta(\Phi(r_1C)) = r_2C$ for every infinity-side $C$. `horient0`: $r_1C = \Phi(r_2C)$ for every zero-side $C$.
--
--   Under these hypotheses, for every place $V$ of $F_M$ at least one of the following four alternatives holds.
--
--   First, $V$ is cuspidal (`JHPlaceSpecialization.IsCuspidal`): for every $x \in F_M$ whose Laurent expansion is `jqModC (AlgebraicClosure ℚ)` and every $a \in A$, $\operatorname{ord}_V\bigl(x - a\bigr) \le 0$.
--
--   Second, $r_1V$ is fixed, that is $\Phi(\delta(\Phi(r_1V))) = r_1V$, and $r_1V$ is affine, that is some $x \in \bar F$ with Laurent expansion `jqModC κ` has a value in $\kappa$ at $r_1V$.
--
--   Third, $V$ is strict of the first kind (`Psp.IsStrictFst`): $\delta(\Phi(r_1V)) = r_2V$ and $r_1V$ is not fixed.
--
--   Fourth, $V$ is strict of the second kind (`Psp.IsStrictSnd`): $r_1V = \Phi(r_2V)$ and $r_2V$ is not fixed.
--
--   This is the typology, or place trichotomy, for the function field of $X_H(M)$ with $p$ exactly dividing $M$: every place either lies over a cusp, or reduces to a fixed point of the diamond-twisted Frobenius involution lying in the affine part, or is strictly of one of the two kinds corresponding to the two components of the mod-$p$ fibre. It is used by the three subsequent existence results producing principal divisors with prescribed value $-1$ and support avoiding the bad locus, on the infinity/first-kind side, on the zero/second-kind side, and in the mixed case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_or_fixed_and_isAffinePlace_or_isStrictFst_or_isStrictSnd.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Classical

theorem ModularCurve.JHPlaceSpecialization.isCuspidal_or_fixed_and_isAffinePlace_or_isStrictFst_or_isStrictSnd
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
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V ∨
      (JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) ∧
        JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V)) ∨
      Psp.IsStrictFst α β hα hβ δ V ∨ Psp.IsStrictSnd α β hα hβ δ V := by sorry
