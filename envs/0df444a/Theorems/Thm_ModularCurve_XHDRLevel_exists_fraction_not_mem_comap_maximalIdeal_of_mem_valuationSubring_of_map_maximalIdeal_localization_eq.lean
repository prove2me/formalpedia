-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq
-- name    : ModularCurve.XHDRLevel.exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/c683182b-ef3b-557f-aa18-91a627428cc7
-- title:
--   Elements of W as chart fractions with denominator off r₀
-- statement:
--   Fix a prime $p$ and a level $M$ with $p \mid M$ (with $M$ and $M/p$ nonzero) and a subgroup $H \le (\mathbb{Z}/M)^\times$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ belongs to `A.nonunits`, with residue field of characteristic $p$ and algebraically closed, made an algebra over the base ring `R p` by a ring map $\rho$ compatible with the structure map $R p \to \overline{\mathbb{Q}}$. Let $B$ be a commutative $R p$-algebra that is flat and of finite type, put $T = A \otimes_{R p} B$, and let $F =$ `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the function field of $X_H(M)$ inside Laurent series over $\overline{\mathbb{Q}}$. Let $W$ be a valuation subring of $F$ and $\gamma : T \to F$ an injective ring homomorphism with image inside $W$, such that every $e \in F$ satisfies $e\,\gamma(s) = \gamma(a)$ for some $a, s \in T$ with $s \neq 0$, and such that $\gamma$ carries $a \in A$, viewed in $T$ through the left inclusion, to the constant $a \in \overline{\mathbb{Q}} \subseteq F$. Assume all such constants lie in $W$, that a constant $a$ lies in the maximal ideal of $W$ exactly when $a$ lies in the maximal ideal of $A$, and that the constant $p$ lies in `W.nonunits`. Let $\mathfrak{r}_0$ be an ideal of $T$, assumed prime, characterised by $t \in \mathfrak{r}_0 \iff \gamma(t) \in \mathfrak{m}_W$, and assume that the image of $\mathfrak{m}_A$ under $A \to T \to T_{\mathfrak{r}_0}$ generates the maximal ideal of $T_{\mathfrak{r}_0}$. Then every $h \in W$ admits $a, c \in T$ with $c \notin \mathfrak{r}_0$ and $h\,\gamma(c) = \gamma(a)$.
--
--   This is the inclusion $W \subseteq \gamma(T_{\mathfrak{r}_0})$, the harder half of the identification of a Gauss-type valuation ring of the function field of $X_H(M)$ with the localisation of a chart ring $A \otimes B$ of a Deligne–Rapoport model at the prime cutting out a branch. It is used in the analysis of crossing primes and of regular prolongations on the model at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.exists_fraction_not_mem_comap_maximalIdeal_of_mem_valuationSubring_of_map_maximalIdeal_localization_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥A] (halg : algebraMap (R p) ↥A = ρ)
    (B : Type) [CommRing B] [Algebra (R p) B] [Algebra.FiniteType (R p) B] [Module.Flat (R p) B]
    (W : ValuationSubring ↥(xHFunctionFieldBar M H))
    (γ : (↥A ⊗[R p] B) →+* ↥(xHFunctionFieldBar M H)) (hγG : ∀ t, γ t ∈ W)
    (hγinj : Function.Injective γ)
    (hγfrac : ∀ e : ↥(xHFunctionFieldBar M H), ∃ a s : (↥A ⊗[R p] B), s ≠ 0 ∧ e * γ s = γ a)
    (hγA : ∀ a : ↥A, γ (Algebra.TensorProduct.includeLeftRingHom a) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))
    (hWA : ∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) ∈ W)
    (hW𝔪 : ∀ a : ↥A, (⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ), hWA a⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W ↔
      a ∈ IsLocalRing.maximalIdeal ↥A)
    (hpW : (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p : AlgebraicClosure ℚ)) ∈ W.nonunits)
    (𝔯₀ : Ideal (↥A ⊗[R p] B)) (h𝔯₀def : ∀ t, t ∈ 𝔯₀ ↔ (⟨γ t, hγG t⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W)
    [h𝔯₀ : 𝔯₀.IsPrime]
    (hmin : (IsLocalRing.maximalIdeal ↥A).map ((algebraMap (↥A ⊗[R p] B) (Localization.AtPrime 𝔯₀)).comp
        (Algebra.TensorProduct.includeLeft (R := R p) (S := R p) (A := ↥A) (B := B)).toRingHom) =
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔯₀))
    (h : ↥(xHFunctionFieldBar M H)) (hh : h ∈ W) :
    ∃ a c : (↥A ⊗[R p] B), c ∉ 𝔯₀ ∧ h * γ c = γ a := by sorry
