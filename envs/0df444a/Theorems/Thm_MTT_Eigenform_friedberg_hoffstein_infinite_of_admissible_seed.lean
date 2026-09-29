-- Prove2me | Theorems.Thm_MTT_Eigenform_friedberg_hoffstein_infinite_of_admissible_seed
-- name    : MTT.Eigenform.friedberg_hoffstein_infinite_of_admissible_seed
-- status  : Open
-- author  : @riccardo.brasca
-- created : 2026-09-26T20:02:14.813498+00:00
-- url     : https://prove2.me/theorems/c521b852-43bc-40e9-a94f-29bec777b4e7
-- title:
--   Infinitely many nonvanishing quadratic twists with the local type of an admissible seed
-- statement:
--   Let $N>0$, let $k\ge2$ be even, and let $f$ be a normalized algebraic cuspidal Hecke eigenform at the least positive level in its Hecke system, with arbitrary nebentype and a fixed complex embedding. Fix $d>0$ and a primitive exact-order-two character $\eta_0$ whose modulus $m_0$ is coprime to $Nd$. If the embedded coefficients of $f$ are real, assume that the actual twist $F_0=f_{\eta_0^{-1}}$ satisfies
--
--   $$F_0\!\left(\frac{i}{Nm_0^2t}\right)=(Nm_0^2)^{k/2}t^k\overline{F_0(it)}\qquad(t>0).$$
--
--   There are infinitely many primitive Dirichlet characters $\eta$ such that
--
--   $$\operatorname{ord}(\eta)=2,\qquad (Nd,\operatorname{cond}\eta)=1,\qquad L(f,\eta,k/2)\ne0,$$
--
--   and such that their local types agree with the seed at the prescribed places:
--
--   $$\eta(-1)=\eta_0(-1),\qquad \eta(p)=\eta_0(p)\quad\text{for every prime }p\mid Nd.$$
--
--   This is the prescribed-local-type Friedberg–Hoffstein theorem over the rationals. The positive-root-number hypothesis is imposed only in the self-dual case. It does not assert existence of an admissible seed.
--
--   **Formalization Note.** The central value and inverse twist are the original mission Mellin constructions. Reality of all embedded coefficients describes self-duality at minimal level. Infinite families are represented by primitive characters together with their positive levels. The classical-to-automorphic and Mellin comparisons belong to this open analytic input.
-- source:
--   Friedberg--Hoffstein, Nonvanishing theorems for automorphic L-functions on GL(2), Ann. of Math. 142 (1995), 385--423, https://doi.org/10.2307/2118638. Precise prescribed-local-type form inspected in Anandavardhanan--Prasad, A local-global question in automorphic forms, Compositio Math. 149 (2013), Theorem 10.6, printed p.986, https://www.math.iitb.ac.in/~dprasad/comp2013.pdf. Specialization to Q and the primitive holomorphic representation of f: prescribe infinity and primes dividing Nd, retain the positive root number for self-dual f, and pass to unique primitive Dirichlet representatives. Unramified local quadratic characters are determined by their value at the prime; quadraticity identifies inverse twists with ordinary twists. Infinitude excludes the single trivial character. These specializations and the Mellin comparison are part of the open theorem.

import Definitions.Def_MTT_QuadraticTwistRootNumber

set_option autoImplicit false

open HorizontalPadicL

/-- Prescribed-local quadratic nonvanishing, conditional on an actual quadratic
seed with positive root number when the primitive eigenform is self-dual. -/
theorem MTT.Eigenform.friedberg_hoffstein_infinite_of_admissible_seed
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (hmin : f.HasMinimalLevel)
    (d : ℕ) (hd : 0 < d) (η₀ : DirichletCharacterWithLevel)
    (hprimitive : η₀.2.IsPrimitive) (horder : orderOf η₀.2 = 2)
    (hcop : Nat.Coprime (N * d) η₀.1.1)
    (hadmissible : f.HasRealCoefficients →
      MTT.HasFrickeRootNumber
        (@MTT.inverseTwist ι f.form η₀.1.1 ⟨Nat.ne_of_gt η₀.1.2⟩ η₀.2)
        (N * η₀.1.1 ^ 2) k 1) :
    Set.Infinite {η : DirichletCharacterWithLevel |
      η.2.IsPrimitive ∧ orderOf η.2 = 2 ∧ Nat.Coprime (N * d) η.2.conductor ∧
      η.2 (-1) = η₀.2 (-1) ∧
      (∀ p : ℕ, p.Prime → p ∣ N * d → η.2 p = η₀.2 p) ∧
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0} := by
  sorry
