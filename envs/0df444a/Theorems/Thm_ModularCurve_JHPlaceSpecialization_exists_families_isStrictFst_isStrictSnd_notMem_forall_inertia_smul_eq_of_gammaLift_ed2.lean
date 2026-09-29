-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq_of_gammaLift_ed2
-- name    : ModularCurve.JHPlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq_of_gammaLift_ed2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/b9bab8cd-6d8d-50d7-888a-106d5cc7abd2
-- title:
--   Inertia-fixed strict places of both kinds avoiding a finite set
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and $H \le (\mathbb{Z}/M)^\times$ is a subgroup containing the kernel of the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$, in the form: every unit $u$ with `ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1` lies in $H$ (`hHp`). Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA : A.LiesOverPrime p`), whose residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. Write $F =$ `xHFunctionFieldBar M H` for the compositum of $\overline{\mathbb{Q}}$ with the function field of $X_H(M)$ inside Laurent series over $\overline{\mathbb{Q}}$, $F' =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ and subgroup the image `infSubgroup p M H hpM` of $H$, and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ attached to the group `JHNeronObjectAtP.ΓN p M H hpM`. Places are in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): valuation subrings of the field containing the base field, proper, and principal ideal rings; `Place.ord` is the associated normalised order function, and $\mathrm{Frob} =$ `qExpFrobeniusPlaceModL κ _ p` denotes the Frobenius operation on places of $\bar F$.
--
--   The remaining data are: an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F$; two $\overline{\mathbb{Q}}$-algebra homomorphisms $\alpha, \beta : F' \to F$, both integral (`hα`, `hβ`); a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`); a self-map $\delta$ of the places of $\bar F$ which, by `hδ`, is the action through `SemilinearAut.ofAlgAut` of the diamond automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM)` evaluated at the lift [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $pb$ to $\Gamma_0(M/p)$; and a finite set $SS$ of pairs of places of $\bar F$ which, by `hSS`, consists exactly of the pairs belonging to `ssNodePairsQExp κ (JHNeronObjectAtP.ΓN p M H hpM) p`, that is of the pairs $(\mathrm{Frob}(v), v)$ with $v$ a supersingular place.
--
--   Next, `Psp : JHPlaceSpecialization p M H hpM A` is a specialization datum: a map `sp` from places of $F'$ to places of $\bar F$, a homomorphism `spPic0` on degree-zero divisor class groups, and the structure fields `d0_qexp`, `d4`, `d5`, `d6_inertia`, `d6_frobenius`, `spPic0_compat`, which require compatibility of `sp` with coefficientwise reduction of $q$-expansions, surjectivity of `sp`, existence of a reduction of each principal divisor, invariance of `sp` under the arithmetic Galois action of the inertia subgroup of $A$, its transformation into $\mathrm{Frob}$ under a Frobenius element at $p$, and compatibility of `spPic0` with pushforward of divisors. Also `Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ` carries two regular prolongations $R_1, R_2$ of $A$ to $F$ with residue maps to $\bar F$, together with the compatibility of the residue map of $R_1$ with coefficientwise reduction of Laurent series over $A$, and the requirements that $f \in R_2$.`integers` if and only if $\theta f \in R_1$.`integers` and that the $R_2$-residue of $f$ equals the $R_1$-residue of $\theta f$. The two readings of a place $W$ of $F$ are $r_1(W) =$ `Psp.reduceFst α hα W` $=$ `sp` of the restriction of $W$ along $\alpha$, and $r_2(W) =$ `Psp.reduceSnd β hβ δ W` $= \delta($`sp` of the restriction of $W$ along $\beta)$. The place $W$ is strict of the first kind (`Psp.IsStrictFst`) when $\delta(\mathrm{Frob}(r_1(W))) = r_2(W)$ and $r_1(W)$ is not `Fixed` for $\delta$ (where `Fixed δ v` means $\mathrm{Frob}(\delta(\mathrm{Frob}(v))) = v$), and strict of the second kind (`Psp.IsStrictSnd`) when $r_1(W) = \mathrm{Frob}(r_2(W))$ and $r_2(W)$ is not `Fixed`.
--
--   The hypotheses on these data are the following blocks, whose contents are summarised here. `hTD` is the type dichotomy: for every place $W$ of $F$, either $r_1(W) = \mathrm{Frob}(r_2(W))$ or $\delta(\mathrm{Frob}(r_1(W))) = r_2(W)$. `hmodel` is `Rpd.IsModel`, the conjunction of the two divisor laws (for $f$ lying in both prolongations with nonzero residues and $D$ the divisor of $f$, the pushforward under $r_1$ of the part of $D$ supported on places strict of the first kind agrees, at every place not `Fixed` for $\delta$, with the order of the $R_1$-residue of $f$, and symmetrically for $r_2$, the second kind and the $R_2$-residue) and the two cusp laws (the same comparison for the parts of $D$ supported on the `IsInftySide` places, read through $r_1$, and on the `IsZeroSide` places, read through $r_2$). `hO` is `Rpd.OrderLawFixed`: at a place $v$ of $\bar F$ which is `Fixed` for $\delta$ and is an affine place in the sense of `IsAffinePlace` (the modular invariant, the element of $\bar F$ with $q$-expansion `jqModC κ`, takes a value in $\kappa$ at $v$), the pushforward of the full divisor of $f$ under $r_1$ equals the order of the $R_1$-residue of $f$ at $v$ plus the order of the $R_2$-residue at $\delta(\mathrm{Frob}(v))$. `hRL` is `Rpd.RegularityLaw` for $SS$ (two clauses: non-negativity of the two residue orders at fixed affine places, and existence of common values at the members of $SS$, under the assumption that $f$ has non-negative order at all places with the prescribed first reading). `hNV` is `Rpd.NodeValueLaw` for $SS$: at a pair $s \in SS$ not met by the divisor of $f$ in the prescribed sense, the two residues take a common nonzero value at $s.1$ and $s.2$.
--
--   The shape hypotheses are `hα_coe`, that $\alpha$ is the identity on $q$-expansions, and `hβ_coe`, that $\beta$ replaces the $q$-expansion of $u$ by `qExpand _ p` of it; `hθgal`, that $\theta$ commutes with the arithmetic Galois action `arithmeticGalois (xHFunctionField M H) σ` for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$; and `hβθ`, that $\beta$ is $\alpha$ followed by $\theta$.
--
--   The local laws `hLFst` and `hLSnd` are mirror-image conditions. `hLFst` requires: for all places $Q \ne Q'$ of $F$, both strict of the first kind, with $r_1(Q') = r_1(Q)$ and $r_1(Q)$ an affine place, for every natural number $n$ whose image in $\kappa$ is nonzero, for every $g$ in $R_1$.`integers` with nonzero $R_1$-residue such that $\mathrm{ord}_Q(g) = -n$, $\mathrm{ord}_{Q'}(g) = n$ and $\mathrm{ord}_W(g) = 0$ for every further place $W$ strict of the first kind with $r_1(W) = r_1(Q)$, and for every $e \in A$ and $\varepsilon$ in $R_1$.`integers` with nonzero $R_1$-residue such that $g = 1 + e\,\varepsilon$, the inequality $-1 \le \mathrm{ord}_{r_1(Q)}$ of the $R_1$-residue of $\varepsilon$ holds. `hLSnd` is the same statement with $r_1$, strictness of the first kind and $R_1$ replaced by $r_2$, strictness of the second kind and $R_2$.
--
--   Finally, `hUnit` asserts the existence of $u_1, u_2 \in F$ and divisors $D_1, D_2$ on $F$ over $\overline{\mathbb{Q}}$ with $D_1(W) = \mathrm{ord}_W(u_1)$ and $D_2(W) = \mathrm{ord}_W(u_2)$ for all places $W$, such that: $u_1$ and $u_1^{-1}$ lie in $R_1$.`integers`, the $R_1$-residue of $u_1$ is nonzero, at every place $v$ of $\bar F$ not `Fixed` for $\delta$ the pushforward under $r_1$ of `Psp.fstDiv` of $D_1$ takes the value $\mathrm{ord}_v$ of that residue, and at every `IsInftySide` place $C$ of $F$ the pushforward under $r_1$ of the restriction of $D_1$ to the `IsInftySide` places takes at $r_1(C)$ the value $\mathrm{ord}_{r_1(C)}$ of that residue; for every nonzero $f \in F$ there are $m \ne 0$ in $\mathbb{N}$ and $j \in \mathbb{Z}$ with $f^m u_1^{j}$ in $R_2$.`integers` and with nonzero $R_2$-residue; the mirror-image conditions for $u_2$, namely $u_2, u_2^{-1} \in R_2$.`integers` with nonzero $R_2$-residue, the comparison of the pushforward under $r_2$ of `Psp.sndDiv` of $D_2$ with the order of that residue at places not `Fixed`, and the corresponding cusp comparison over the `IsZeroSide` places; and for every nonzero $f \in F$ there are $m \ne 0$ and $j \in \mathbb{Z}$ with $f^m u_2^{j}$ in $R_1$.`integers` and with nonzero $R_1$-residue.
--
--   Under these hypotheses, for every finite set $B$ of places of $\bar F$ and all natural numbers $m_1, m_2$ there exist families $Q_1 : \mathrm{Fin}\,m_1 \to$ places of $F$ and $Q_2 : \mathrm{Fin}\,m_2 \to$ places of $F$ such that: every $Q_1(i)$ is strict of the first kind; every $Q_2(j)$ is strict of the second kind; the map $i \mapsto r_1(Q_1(i))$ is injective; the map $j \mapsto r_2(Q_2(j))$ is injective; $r_1(Q_1(i)) \notin B$ for every $i$; $r_2(Q_2(j)) \notin B$ for every $j$; for every $i$ and every $\sigma$ in `A.inertiaSubgroupIn ℚ` the arithmetic Galois action of $\sigma$ fixes $Q_1(i)$; and for every $j$ and every such $\sigma$ the arithmetic Galois action of $\sigma$ fixes $Q_2(j)$. No relation between the two families beyond these conjuncts is asserted.
--
--   This is an avoidance and rigidity lemma for the geometry of the special fibre at a prime $p$ exactly dividing the level $M$: it produces arbitrarily many places of the base-changed function field of $X_H(M)$ that are strict of each of the two kinds, have pairwise distinct reductions lying outside a prescribed finite set of places of the characteristic-$p$ function field, and are individually fixed by the inertia group at $p$. It serves as the supply of auxiliary places in the subsequent construction of good divisors, of functions with prescribed order one at a strict place, and of the depth and annulus data used in the level-lowering analysis at $p \parallel M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq_of_gammaLift_ed2.lean

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

theorem ModularCurve.JHPlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq_of_gammaLift_ed2
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

    (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (m₁ m₂ : ℕ) :
    ∃ (Q₁ : Fin m₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂ : Fin m₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁ i)) ∧ (∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂ j)) ∧
      (Function.Injective fun i => Psp.reduceFst α hα (Q₁ i)) ∧
      (Function.Injective fun j => Psp.reduceSnd β hβ δ (Q₂ j)) ∧
      (∀ i, Psp.reduceFst α hα (Q₁ i) ∉ B) ∧ (∀ j, Psp.reduceSnd β hβ δ (Q₂ j) ∉ B) ∧
      (∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • Q₁ i = Q₁ i) ∧
      (∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • Q₂ j = Q₂ j) := by sorry
