-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_compactPicture_eq_bot_of_transitionStable_of_bottom_eq_bot
-- name    : LanglandsTunnell.CubicInduction.compactPicture_eq_bot_of_transitionStable_of_bottom_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/c0382180-59eb-5693-9c11-b942afccd53e
-- title:
--   Transition-stable harmonic families vanish once their bottom degree does
-- statement:
--   Let $\tau,\tau_3$ be real numbers. Write $\Xi_\nu(p)$, for $\nu:\mathrm{Fin}\,3\to\mathbb{C}$ and $p\in\mathbb{C}[x_0,x_1,x_2]$, for the $3\times 3$ matrix of polynomials whose diagonal entry at $c$ is $2(\nu_c+\rho_c)\,p$ with $\rho=(1,0,-1)$ and whose entry at $c\ne d$ is $-(x_{\max(c,d)}\,\partial_{\min(c,d)}p-x_{\min(c,d)}\,\partial_{\max(c,d)}p)$; put $\mathrm{lower}_2(M)=\sum_{c,d}\partial_c\partial_d M_{cd}$, $\mathrm{lower}_1(M)=\sum_{a,b,c,d}\tfrac{(a-c)(c-d)(d-a)}{2}\,x_c\,\partial_b\partial_d M_{ab}$ (indices read as complex numbers), and $\mathrm{same}_2(M)=6q-\bigl(\sum_i x_i^2\bigr)\bigl(\sum_i\partial_i^2 q\bigr)$ where $q=\sum_{c,d}x_c\,\partial_d M_{cd}$. Set $\nu_{12}=(-\tfrac12+i\tau,\ \tfrac12+i\tau,\ i\tau_3)$ and $\nu_{13}=(-\tfrac12+i\tau,\ i\tau_3,\ \tfrac12+i\tau)$. The assertion is a conjunction of four implications, each about a family $S:\mathbb{N}\to$ submodules of $\mathbb{C}[x_0,x_1,x_2]$ such that every $p\in S_\ell$ is homogeneous of degree $\ell$ and satisfies $\sum_i\partial_i^2p=0$, and such that for all $\ell$ and all $p\in S_\ell$ one has $\mathrm{lower}_2(\Xi_\nu p)\in S_{\ell-2}$ and $\mathrm{lower}_1(\Xi_\nu p)\in S_{\ell-1}$ (truncated subtraction on $\mathbb{N}$). For $\nu=\nu_{12}$, respectively $\nu=\nu_{13}$: (i) if $S_0\le\mathbb{C}\cdot 1$, $S_1=0$, $S_2\le\langle x_0^2-x_2^2,\ x_1^2-x_2^2\rangle$, $\mathrm{same}_2(\Xi_\nu p)\in S_2$ for all $p\in S_2$, and $S_0=0$, then $S_\ell=0$ for all $\ell$; (ii) if $S_0=0$, $S_1\le\mathbb{C}\cdot x_2$ (resp. $\mathbb{C}\cdot x_1$), $S_2\le\mathbb{C}\cdot x_0x_1$ (resp. $\mathbb{C}\cdot x_0x_2$), and $S_1=0$, then $S_\ell=0$ for all $\ell$.
--
--   This is the induction step in the analysis of the compact picture of a principal series of $\mathrm{GL}_3(\mathbb{R})$ with half-integral spectral parameter, the $K$-isotypic components being modelled by harmonic homogeneous polynomials in three variables and the lowering transitions by the operators $\mathrm{lower}_2\circ\Xi_\nu$, $\mathrm{lower}_1\circ\Xi_\nu$ and $\mathrm{same}_2\circ\Xi_\nu$. It is used in the proof that the relevant exponential coefficients vanish on the line $\mathrm{Re}\,\nu=\tfrac12$, within the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_compactPicture_eq_bot_of_transitionStable_of_bottom_eq_bot.lean

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.compactPicture_eq_bot_of_transitionStable_of_bottom_eq_bot
    (τ τ₃ : ℝ) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    let same₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
        (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
          (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
            (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))
    let ν₁₂ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, 1 / 2 + τ * Complex.I, τ₃ * Complex.I]
    let ν₁₃ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, τ₃ * Complex.I, 1 / 2 + τ * Complex.I]
    (∀ S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
        p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) →
      S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} → S 1 = ⊥ →
      S 2 ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν₁₂ p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν₁₂ p) ∈ S (ℓ - 1)) →
      (∀ p ∈ S 2, same₂ (Ξ ν₁₂ p) ∈ S 2) →
      S 0 = ⊥ → ∀ ℓ, S ℓ = ⊥) ∧
    (∀ S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
        p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) →
      S 0 = ⊥ → S 1 ≤ Submodule.span ℂ {(MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} →
      S 2 ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} →
      (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν₁₂ p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν₁₂ p) ∈ S (ℓ - 1)) →
      S 1 = ⊥ → ∀ ℓ, S ℓ = ⊥) ∧
    (∀ S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
        p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) →
      S 0 ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} → S 1 = ⊥ →
      S 2 ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν₁₃ p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν₁₃ p) ∈ S (ℓ - 1)) →
      (∀ p ∈ S 2, same₂ (Ξ ν₁₃ p) ∈ S 2) →
      S 0 = ⊥ → ∀ ℓ, S ℓ = ⊥) ∧
    (∀ S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
        p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) →
      S 0 = ⊥ → S 1 ≤ Submodule.span ℂ {(MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} →
      S 2 ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} →
      (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν₁₃ p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν₁₃ p) ∈ S (ℓ - 1)) →
      S 1 = ⊥ → ∀ ℓ, S ℓ = ⊥) := by sorry
