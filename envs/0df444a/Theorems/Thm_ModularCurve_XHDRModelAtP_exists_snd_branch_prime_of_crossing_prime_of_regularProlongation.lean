-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation
-- name    : ModularCurve.XHDRModelAtP.exists_snd_branch_prime_of_crossing_prime_of_regularProlongation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/a2427e8d-f4ee-51aa-968c-72dbe331960b
-- title:
--   Second branch prime at a supersingular crossing
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$; assume $j$ lies in the $q$-expansion function field of $\mathrm{SL}(2,\mathbb{Z})$ and let $\mathfrak{X}$ be a Deligne–Rapoport datum `XHDRModelAtP` for $X_H(M)$ over $R_p$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit, with algebraically closed residue field of characteristic $p$, together with $\rho : R_p \to A$ compatible with the structure maps and making $A$ an $R_p$-algebra. Write $T = A \otimes_{R_p} \mathrm{chartAlgFin}$. Further data: an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $\overline{F} =$ `xHFunctionFieldBar M H` which, by `hwgen`, induces on places the action of $\mathfrak{X}.w$; a ring map $\gamma : T \to \overline{F}$ with $\gamma(a \otimes b) = a\cdot b$ on Laurent series, injective, with every element of $\overline{F}$ of the form $\gamma a/\gamma s$ ($s \ne 0$); a point $n$ of the fibre product of $\mathfrak{X}.\mathrm{comp}$ at $0$ and $1$; a prime $\mathfrak{Q} \subset T$ arising as the kernel of a map $\chi_\kappa : T \to \kappa_A$ restricting to the residue map on $A$, together with a $\kappa_A$-section $t$ of the special fibre compatible with $\chi_\kappa$ and carrying the closed point to the image of $n$; a regular prolongation $R_g$ of $A$ to $\overline{F}$ with residue field `JHNeronObjectAtP.Fbar p M H hpM` $\kappa_A$, whose integers are exactly the $f$ admitting Laurent series $x,y$ over $A$ with $y$ of nonzero reduction and $fy = x$, whose residue on reductions of integral Laurent series is coefficientwise reduction, and with $\gamma(T) \subseteq R_g$; and the ideal $\mathfrak{r}_0 = \gamma^{-1}(\mathfrak{m}_{R_g})$, assumed prime. The conclusion is the existence of a prime $\mathfrak{r}_1 \subset T$ with $\mathfrak{r}_0, \mathfrak{r}_1 \subseteq \mathfrak{Q}$, the two incomparable, with $\mathfrak{m}_A T = \mathfrak{r}_0 \cap \mathfrak{r}_1$, such that for $h \in \overline{F}$ one has $h\,\gamma c = \gamma a$ for some $a, c \in T$ with $c \notin \mathfrak{r}_1$ if and only if $\theta h$ satisfies the Gauss condition above, and such that $\mathfrak{m}_A$ generates the maximal ideal of the localisation of $T$ at $\mathfrak{r}_0$.
--
--   This is the branch dictionary at a supersingular crossing point of the Deligne–Rapoport model of $X_H(M)$ in residue characteristic $p$: the two minimal primes over $\mathfrak{m}_A T$ through the crossing correspond to the two components, one being the Gauss ring of $q$-expansions and the other its transform under the Atkin–Lehner involution realised by $\theta$. It feeds the statement [`ModularCurve.XHDRModelAtP.exists_branch_primes_gauss_iff_and_hasValue_of_crossing_prime`](thm.html#ModularCurve.XHDRModelAtP.exists_branch_primes_gauss_iff_and_hasValue_of_crossing_prime), which packages the crossing data used in the analysis of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_snd_branch_prime_of_crossing_prime_of_regularProlongation.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_snd_branch_prime_of_crossing_prime_of_regularProlongation
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥A] (halg : algebraMap (R p) ↥A = ρ)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))

    (𝔔 : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔔 : 𝔔.IsPrime) (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (hker : RingHom.ker χκ = 𝔔)
    (hχA : χκ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = IsLocalRing.residue ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n)
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hγG : ∀ t : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), γ t ∈ Rg.integers)
    (hγinj : Function.Injective γ)
    (hγfrac : ∀ e : ↥(xHFunctionFieldBar M H), ∃ a s : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), s ≠ 0 ∧ e * γ s = γ a)
    (𝔯₀ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (h𝔯₀def : ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥Rg.integers) ∈ IsLocalRing.maximalIdeal ↥Rg.integers)
    [h𝔯₀p : 𝔯₀.IsPrime] :
    ∃ 𝔯₁ : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), 𝔯₁.IsPrime ∧ 𝔯₀ ≤ 𝔔 ∧ 𝔯₁ ≤ 𝔔 ∧ ¬ 𝔯₀ ≤ 𝔯₁ ∧ ¬ 𝔯₁ ≤ 𝔯₀ ∧
      (IsLocalRing.maximalIdeal ↥A).map (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = 𝔯₀ ⊓ 𝔯₁ ∧
      (∀ h : ↥(xHFunctionFieldBar M H),
        (∃ a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)), c ∉ 𝔯₁ ∧ h * γ c = γ a) ↔
        (∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((θ h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)) ∧
      (IsLocalRing.maximalIdeal ↥A).map ((algebraMap (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) (Localization.AtPrime 𝔯₀)).comp
          (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) =
        IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯₀) := by sorry
