-- Prove2me | Theorems.Thm_MvPolynomial_exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric
-- name    : MvPolynomial.exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/3d3c14c2-4347-592f-8fac-c5406ea2ebcd
-- title:
--   Symmetric homogeneous 2-cocycles are coboundaries (Lazard)
-- statement:
--   Let $R$ be a commutative ring, let $\sigma$ be a finite type, and let $n$ be a natural number whose image in $R$ is a unit. Let $\Gamma$ be a polynomial in the variables indexed by $\sigma \oplus \sigma$ over $R$, thought of as $\Gamma(X,Y)$ with the left copy of $\sigma$ indexing the $X$-variables and the right copy the $Y$-variables. Assume: $\Gamma$ is homogeneous of degree $n$; $\Gamma$ is symmetric, in the sense that renaming the variables along the swap of the two summands leaves $\Gamma$ unchanged; and $\Gamma$ satisfies the $2$-cocycle identity in the polynomial ring on $\sigma \oplus (\sigma \oplus \sigma)$ with variables written $X,Y,Z$, namely that the four substitutions $(X,Y)\mapsto(Y,Z)$, $(X+Y,Z)$, $(X,Y+Z)$ and $(X,Y)$ into $\Gamma$, evaluated through the respective $R$-algebra maps, satisfy $\Gamma(Y,Z)-\Gamma(X+Y,Z)+\Gamma(X,Y+Z)-\Gamma(X,Y)=0$. Then there exists a polynomial $h$ in the variables indexed by $\sigma$ over $R$, homogeneous of degree $n$, such that $\Gamma$ equals the substitution of $X_s + Y_s$ for the $s$-th variable of $h$ minus the two renamings of $h$ into the left and right copies of $\sigma$; that is, $\Gamma(X,Y) = h(X+Y) - h(X) - h(Y)$.
--
--   This is Lazard's comparison lemma in the homogeneous several-variable form: symmetric homogeneous $2$-cocycles of degree $n$ are coboundaries as soon as $n$ is invertible in the base ring. It is used in the construction of the logarithm of a multivariable formal group law over an adically complete ring, via [`MvFormalGroup.exists_rescaledLog_of_isAdicComplete`](thm.html#MvFormalGroup.exists_rescaledLog_of_isAdicComplete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem MvPolynomial.exists_isHomogeneous_eq_sub_sub_of_cocycle_of_symmetric
    {R : Type u} [CommRing R] {σ : Type v} [Finite σ] (n : ℕ) (hn : IsUnit (n : R))
    (Γ : MvPolynomial (σ ⊕ σ) R) (hhom : Γ.IsHomogeneous n)
    (hsymm : MvPolynomial.rename Sum.swap Γ = Γ)
    (hcoc :
      MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inr (Sum.inl s)) : MvPolynomial (σ ⊕ (σ ⊕ σ)) R))
          (fun s => MvPolynomial.X (Sum.inr (Sum.inr s)))) Γ
        - MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inl s) + MvPolynomial.X (Sum.inr (Sum.inl s)) :
            MvPolynomial (σ ⊕ (σ ⊕ σ)) R)) (fun s => MvPolynomial.X (Sum.inr (Sum.inr s)))) Γ
        + MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inl s) : MvPolynomial (σ ⊕ (σ ⊕ σ)) R))
            (fun s => MvPolynomial.X (Sum.inr (Sum.inl s)) + MvPolynomial.X (Sum.inr (Sum.inr s)))) Γ
        - MvPolynomial.aeval (Sum.elim (fun s => (MvPolynomial.X (Sum.inl s) : MvPolynomial (σ ⊕ (σ ⊕ σ)) R))
            (fun s => MvPolynomial.X (Sum.inr (Sum.inl s)))) Γ = 0) :
    ∃ h : MvPolynomial σ R, h.IsHomogeneous n ∧
      Γ = MvPolynomial.aeval (fun s => (MvPolynomial.X (Sum.inl s) + MvPolynomial.X (Sum.inr s) : MvPolynomial (σ ⊕ σ) R)) h
        - MvPolynomial.rename Sum.inl h - MvPolynomial.rename Sum.inr h := by sorry
