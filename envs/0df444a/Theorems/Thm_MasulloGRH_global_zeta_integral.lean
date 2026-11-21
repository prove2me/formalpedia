-- Prove2me | Theorems.Thm_MasulloGRH_global_zeta_integral
-- name    : MasulloGRH.global_zeta_integral
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T04:39:04.660045+00:00
-- url     : https://prove2.me/theorems/65d9b3ff-6c34-4f26-b112-bcd8a09403d6
-- title:
--   Theorem 3.2.2.1 (1)–(2) — the global zeta integral $Z(f,c)$: convergence, continuation, residues and functional equation
-- statement:
--   This is the main theorem of Tate's thesis for the idele class group, in the form used by the draft.
--
--   Let $F$ be a number field, $f\in\mathcal S(\mathbb A_F)$, and $c_0$ a quasi-character of $C_F$ with abscissa $\sigma(c_0)$. Write $c_s=c_0|\cdot|_F^s$, so $\sigma(c_s)=\sigma(c_0)+\operatorname{Re}(s)$, and let
--   $$Z(f,c)=\int_{\mathrm{GL}_1(\mathbb A_F)}f(g)c(g)\,d\mu(g),\qquad L(f,c)=\int_{C_F}\Phi_F(f)(g)c(g)\,d\bar\mu(g)$$
--   with the Tamagawa measures $\mu$, $\bar\mu$ and $\Phi_F(f)(g)=\sum_{\xi\in F^\times}f(\xi g)$.
--
--   1. For $\sigma(c_s)>1$ the integral $Z(f,c_s)$ converges absolutely, and $s\mapsto Z(f,c_s)$ is holomorphic on this half-plane.
--   2. $s\mapsto Z(f,c_s)$ extends to a meromorphic function on $\mathbb C$. It is holomorphic at every $s$ with $c_s\neq1$ and $c_s\neq|\cdot|_F$. At a point $s_0$ with $c_{s_0}=1$ it has at most a simple pole, with residue $-\mu_1(C_F^1)\,f(0)$; at a point $s_0$ with $c_{s_0}=|\cdot|_F$ it has at most a simple pole, with residue $\mu_1(C_F^1)\,\widehat f(0)$.
--   3. Functional equation: as meromorphic functions of $s$,
--   $$Z(f,c_s)=Z(\widehat f,\widehat{c_s}),\qquad\widehat c=|\cdot|_F\,c^{-1}.$$
--   4. For $\sigma(c_s)>1$ the integral $L(f,c_s)$ converges absolutely and $L(f,c_s)=Z(f,c_s)$.
--   5. If $f(0)=\widehat f(0)=0$, or if $c_0$ is not trivial on $C_F^1$, then $L(f,c_s)$ converges absolutely for every $s\in\mathbb C$ and $s\mapsto L(f,c_s)$ is entire.
--
--   The theorem identifies the Mellin transform of the adelic $\theta$-function with Tate's zeta integral and gives its analytic continuation; the completed Hecke $L$-functions arise from it for suitable $f$.
--
--   **Formalization Note** Functions on the Riemann surface $\Omega(C_F)$ are functions of $s$ on each component $\{c_0|\cdot|_F^s\}$. The continuation is a function in meromorphic normal form; the residue at $s_0$ is $\lim_{s\to s_0}(s-s_0)M(s)$. In item 3 the right side is the continuation of $u\mapsto Z(\widehat f,\widehat{c_0}|\cdot|_F^u)$ evaluated at $u=-s$. The local uniformity of the convergence of the integrals is not stated separately. The components of $\Omega(C_F)$ other than $\Omega(C_F)(1)$ are those of the $c_0$ that are not trivial on the ideles of norm $1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Chapter 3, §3.2.2, Theorem 3.2.2.1 (Idelic Mellin transform of global adelic θ-functions), parts (1), (1a), (1b), (2), (2a), (2b) and the identity L(f,c) = Z(f,c) of part (3), eqs. (3.2.2.1)–(3.2.2.3), pp. 124–125

import Definitions.Def_MasulloGRH_ZetaIntegrals

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain MeasureTheory

theorem global_zeta_integral (F : Type*) [Field F] [NumberField F] (f : AdelicSchwartz F)
    (c₀ : IdeleGroup F → ℂ) (hc : IsQuasiCharacter c₀) :
    ((∀ s : ℂ, 1 < quasiAbscissa c₀ + s.re →
        Integrable (fun g : IdeleGroup F => f.eval (g : AdeleRing (𝓞 F) F) * quasiTwist c₀ s g)
          (tamagawaIdele F)) ∧
      DifferentiableOn ℂ (fun s : ℂ => zetaIntegral f (quasiTwist c₀ s))
        {s : ℂ | 1 < quasiAbscissa c₀ + s.re}) ∧
    (∃ M M' : ℂ → ℂ, MeromorphicNFOn M Set.univ ∧ MeromorphicNFOn M' Set.univ ∧
      (∀ s : ℂ, 1 < quasiAbscissa c₀ + s.re → M s = zetaIntegral f (quasiTwist c₀ s)) ∧
      (∀ s : ℂ, quasiTwist c₀ s ≠ (fun _ => 1) → quasiTwist c₀ s ≠ normQuasiChar 1 →
        AnalyticAt ℂ M s) ∧
      (∀ s₀ : ℂ, quasiTwist c₀ s₀ = (fun _ => 1) →
        Filter.Tendsto (fun s : ℂ => (s - s₀) * M s) (nhdsWithin s₀ {s₀}ᶜ)
          (nhds (-(tamagawaClassVolume F : ℂ) * f.eval 0))) ∧
      (∀ s₀ : ℂ, quasiTwist c₀ s₀ = normQuasiChar 1 →
        Filter.Tendsto (fun s : ℂ => (s - s₀) * M s) (nhdsWithin s₀ {s₀}ᶜ)
          (nhds ((tamagawaClassVolume F : ℂ) * adelicFourier f 0))) ∧
      (∀ s : ℂ, 1 < quasiAbscissa (quasiDual c₀) + s.re →
        M' s = zetaIntegralFun (adelicFourier f) (quasiTwist (quasiDual c₀) s)) ∧
      ∀ s : ℂ, M s = M' (-s)) ∧
    (∀ s : ℂ, 1 < quasiAbscissa c₀ + s.re →
      Integrable (fun x : IdeleClassGroup F => adelicTheta f x.out * quasiTwist c₀ s x.out)
        (tamagawaIdeleClass F) ∧
      thetaMellin f (quasiTwist c₀ s) = zetaIntegral f (quasiTwist c₀ s)) ∧
    ((f.IsPolarFree ∨ ¬ ∀ g : IdeleGroup F, ideleNorm g = 1 → c₀ g = 1) →
      (∀ s : ℂ,
        Integrable (fun x : IdeleClassGroup F => adelicTheta f x.out * quasiTwist c₀ s x.out)
          (tamagawaIdeleClass F)) ∧
      Differentiable ℂ (fun s : ℂ => thetaMellin f (quasiTwist c₀ s))) := by sorry

end MasulloGRH
