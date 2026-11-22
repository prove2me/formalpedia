-- Prove2me | Theorems.Thm_MasulloGRH_global_zeta_integral_corrected
-- name    : MasulloGRH.global_zeta_integral_corrected
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T00:00:07.845158+00:00
-- url     : https://prove2.me/theorems/486fc11d-f468-4f78-a256-e5dbff7626a0
-- title:
--   Theorem 3.2.2.1 (1)–(2), corrected — the global zeta integral $Z(f,c)$: convergence, continuation, residues, functional equation; $L(f,c)$ for $f(0)=\widehat f(0)=0$
-- statement:
--   This is Theorem 3.2.2.1, parts (1)–(2), of the source with one correction: part (2b) is replaced by the statement that is true. The printed part (2b) is refuted by the accepted disproof of `MasulloGRH.global_zeta_integral`.
--
--   **Setting.** $F$ is a number field, $f\in\mathcal S(\mathbb A_F)$, and $c_0$ is a quasi-character of the idele class group $C_F$ (a continuous homomorphism $\mathrm{GL}_1(\mathbb A_F)\to\mathbb C^\times$ trivial on $F^\times$) with abscissa $\sigma(c_0)$, so $|c_0(g)|=|g|_F^{\sigma(c_0)}$. The connected component of $c_0$ in $\Omega(C_F)$ is $\{c_0|\cdot|_F^{s}:s\in\mathbb C\}$, and the statement is written in the coordinate $s$. $\mu$ and $\bar\mu$ are the Tamagawa measures on $\mathrm{GL}_1(\mathbb A_F)$ and $C_F$, $V=\mu_1(C_F^1)$ is the volume (A.3.2.1), $\widehat f$ is the adelic Fourier transform, $\widehat c=|\cdot|_Fc^{-1}$, and
--   $$Z(f,c)=\int_{\mathrm{GL}_1(\mathbb A_F)}f(g)c(g)\,d\mu(g),\qquad L(f,c)=\int_{C_F}\Phi_F(f)(g)c(g)\,d\bar\mu(g).$$
--
--   **(1) Convergence and holomorphy.** For $\sigma(c_0)+\operatorname{Re}s>1$ the function $g\mapsto f(g)\,c_0(g)|g|_F^{s}$ is $\mu$-integrable, and $s\mapsto Z(f,c_0|\cdot|_F^s)$ is holomorphic on this half-plane.
--
--   **(1a), (1b) Continuation, residues, functional equation.** There are meromorphic functions $M,M'$ on $\mathbb C$ (in normal form) such that:
--   - $M(s)=Z(f,c_0|\cdot|_F^s)$ for $\sigma(c_0)+\operatorname{Re}s>1$;
--   - $M$ is holomorphic at every $s$ with $c_0|\cdot|_F^s\ne1$ and $c_0|\cdot|_F^s\ne|\cdot|_F$;
--   - if $c_0|\cdot|_F^{s_0}=1$ then $(s-s_0)M(s)\to-V f(0)$ as $s\to s_0$; if $c_0|\cdot|_F^{s_0}=|\cdot|_F$ then $(s-s_0)M(s)\to V\widehat f(0)$;
--   - $M'(s)=Z(\widehat f,\widehat{c_0}|\cdot|_F^s)$ for $\sigma(\widehat{c_0})+\operatorname{Re}s>1$, and $M(s)=M'(-s)$ for all $s$. This is $Z(f,c)=Z(\widehat f,\widehat c)$, since $\widehat{c_0|\cdot|_F^{s}}=\widehat{c_0}|\cdot|_F^{-s}$.
--   - **(2b), corrected.** If $c_0$ is not trivial on the ideles of norm $1$ (the components of $\Omega(C_F)$ other than $\Omega(C_F)(1)$), then $M$ is entire.
--
--   **(2) and (3) for $\sigma>1$.** For $\sigma(c_0)+\operatorname{Re}s>1$ the function $x\mapsto\Phi_F(f)(x)\,c_0(x)|x|_F^s$ is $\bar\mu$-integrable on $C_F$ and $L(f,c_0|\cdot|_F^s)=Z(f,c_0|\cdot|_F^s)$.
--
--   **(2a).** If $f(0)=\widehat f(0)=0$, then $x\mapsto\Phi_F(f)(x)\,c_0(x)|x|_F^s$ is $\bar\mu$-integrable for every $s\in\mathbb C$ and $s\mapsto L(f,c_0|\cdot|_F^s)$ is entire.
--
--   **What was changed.** The source's (2b) asserts that for $c$ outside $\Omega(C_F)(1)$ the integral $L(f,c)$ converges *absolutely* for every $c$, with no condition on $f$. That fails: as $|x|_F\to0$ one has $\Phi_F(f)(x)\sim|x|_F^{-1}\widehat f(0)-f(0)$, so $|\Phi_F(f)\,c|$ is not integrable when $\sigma(c)\le1$ and $\widehat f(0)\ne0$, whatever the character. What survives is that the polar terms cancel after integration over $C_F^1$, so the meromorphic continuation has no poles; this is the last item of the list above. The formal statement is otherwise identical to `MasulloGRH.global_zeta_integral`. The measures are well defined by `MasulloGRH.tamagawa_measures_wellDefined`.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 3.2.2.1, eqs. (3.2.2.1)–(3.2.2.3), pp. 124–125 (proof pp. 125–128); part (2b) corrected as explained in the statement.

import Definitions.Def_MasulloGRH_ZetaIntegrals

set_option autoImplicit false
namespace MasulloGRH

open NumberField IsDedekindDomain MeasureTheory

theorem global_zeta_integral_corrected (F : Type*) [Field F] [NumberField F]
    (f : AdelicSchwartz F) (c₀ : IdeleGroup F → ℂ) (hc : IsQuasiCharacter c₀) :
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
      (∀ s : ℂ, M s = M' (-s)) ∧
      ((¬ ∀ g : IdeleGroup F, ideleNorm g = 1 → c₀ g = 1) → Differentiable ℂ M)) ∧
    (∀ s : ℂ, 1 < quasiAbscissa c₀ + s.re →
      Integrable (fun x : IdeleClassGroup F => adelicTheta f x.out * quasiTwist c₀ s x.out)
        (tamagawaIdeleClass F) ∧
      thetaMellin f (quasiTwist c₀ s) = zetaIntegral f (quasiTwist c₀ s)) ∧
    (f.IsPolarFree →
      (∀ s : ℂ,
        Integrable (fun x : IdeleClassGroup F => adelicTheta f x.out * quasiTwist c₀ s x.out)
          (tamagawaIdeleClass F)) ∧
      Differentiable ℂ (fun s : ℂ => thetaMellin f (quasiTwist c₀ s))) := by sorry

end MasulloGRH
