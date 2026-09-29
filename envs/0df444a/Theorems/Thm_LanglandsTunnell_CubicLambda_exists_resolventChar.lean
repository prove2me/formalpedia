-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicLambda_exists_resolventChar
-- name    : LanglandsTunnell.CubicLambda.exists_resolventChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/02ba5b50-cfd6-5f18-8966-ba6d3a525311
-- title:
--   Resolvent Hecke character of a non-normal cubic field
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ which is not normal over $\mathbb{Q}$, let $L$ be a number field with $[L:\mathbb{Q}]=2$, and let $E$ be a number field with $[E:\mathbb{Q}]=6$ which is Galois over $\mathbb{Q}$; the rings of integers are equipped with algebra structures $\mathcal{O}_{\mathbb{Q}}\to\mathcal{O}_K,\mathcal{O}_L\to\mathcal{O}_E$, all integral and forming scalar towers over $\mathcal{O}_{\mathbb{Q}}$, so that $E$ contains both $K$ and $L$. Then there is a monoid homomorphism $\theta$ from the ideles $(\mathbb{A}_L)^{\times}$ to $\mathbb{C}^{\times}$ which is a finite-order Hecke character, that is, $\theta$ is trivial on the principal ideles (the image of $L^{\times}$), continuous, and of finite order, and which satisfies the following. (i) For every prime $\mathfrak{q}$ of $\mathcal{O}_L$ and every prime $\mathfrak{Q}$ of $\mathcal{O}_E$ with $\mathfrak{Q}\cap\mathcal{O}_L=\mathfrak{q}$: if the ramification index $e(\mathfrak{Q}/\mathfrak{q})$ equals $1$, then the Euler coefficient of $\theta$ at $\mathfrak{q}$ — the value of $\theta$ at the idele given by a uniformizer at $\mathfrak{q}$ when the local component of $\theta$ is trivial on the units of the completion at $\mathfrak{q}$, and $0$ otherwise — is a primitive root of unity of order the inertia degree $f(\mathfrak{Q}/\mathfrak{q})$; if $e(\mathfrak{Q}/\mathfrak{q})\neq 1$, that Euler coefficient is $0$. (ii) For every prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ and distinct primes $\mathfrak{q},\mathfrak{q}'$ of $\mathcal{O}_L$ above $p$, the Euler coefficients at $\mathfrak{q}$ and $\mathfrak{q}'$ are mutually inverse. (iii) At every real place $u$ of $L$ the archimedean component of $\theta$ has parameters $(0,\,\overline{0}\in\mathbb{Z}/2$ cast to $\mathbb{Z})$, and at every complex place the parameters $(0,0)$; in both cases this says that for all units $x$ of the completion at $u$, $\theta$ composed with the embedding of those units into the ideles takes the value $\lVert x\rVert^{0}\,(x/\lVert x\rVert)^{0}=1$, i.e. the component of $\theta$ at $u$ is trivial.
--
--   This is the existence of the resolvent character: the finite-order Hecke character of the quadratic resolvent $L$ attached by Artin reciprocity to the cyclic cubic extension $E/L$, normalised so that its Euler coefficients record the splitting of $E/L$ prime by prime. It feeds the cubic induction step, where the induced two-dimensional representation attached to a non-normal cubic field is matched with an automorphic object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicLambda_exists_resolventChar.lean

import Definitions.Def_LanglandsTunnell_CubicLambda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.InfinitePlace HeckeCharacter LanglandsTunnell.Converse

theorem LanglandsTunnell.CubicLambda.exists_resolventChar
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
    (E : Type) [Field E] [NumberField E]
    [Algebra (𝓞 ℚ) (𝓞 E)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 E)]
    [Algebra (𝓞 L) (𝓞 E)] [Algebra.IsIntegral (𝓞 L) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 L) (𝓞 E)]
    [Algebra (𝓞 K) (𝓞 E)] [Algebra.IsIntegral (𝓞 K) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 K) (𝓞 E)]
    [IsGalois ℚ E]
    (hK : Module.finrank ℚ K = 3) (hKn : ¬ Normal ℚ K)
    (hL : Module.finrank ℚ L = 2) (hE : Module.finrank ℚ E = 6) :
    ∃ θ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ, IsFiniteOrderHeckeChar L θ ∧
      (∀ (𝔮 : HeightOneSpectrum (𝓞 L)) (𝔔 : HeightOneSpectrum (𝓞 E)), 𝔔.under (𝓞 L) = 𝔮 →
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal = 1 →
          IsPrimitiveRoot (eulerCoeff L θ 𝔮) (𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal)) ∧
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal ≠ 1 → eulerCoeff L θ 𝔮 = 0)) ∧
      (∀ (p : HeightOneSpectrum (𝓞 ℚ)) (𝔮 𝔮' : HeightOneSpectrum (𝓞 L)),
        𝔮.under (𝓞 ℚ) = p → 𝔮'.under (𝓞 ℚ) = p → 𝔮 ≠ 𝔮' →
          eulerCoeff L θ 𝔮' = (eulerCoeff L θ 𝔮)⁻¹) ∧
      (∀ u : InfinitePlace L, u.IsReal → IsArchCompAt L θ u 0 (((0 : ZMod 2)).val : ℤ)) ∧
      (∀ u : InfinitePlace L, u.IsComplex → IsArchCompAt L θ u 0 0) := by sorry
