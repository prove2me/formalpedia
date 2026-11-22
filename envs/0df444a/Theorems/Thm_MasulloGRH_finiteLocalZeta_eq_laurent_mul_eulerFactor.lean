-- Prove2me | Theorems.Thm_MasulloGRH_finiteLocalZeta_eq_laurent_mul_eulerFactor
-- name    : MasulloGRH.finiteLocalZeta_eq_laurent_mul_eulerFactor
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:35:08.842936+00:00
-- url     : https://prove2.me/theorems/2dd64923-d87b-430d-863b-8713a41cfece
-- title:
--   (6.3.1.4), Tate — for $f\in\mathcal S(F_v)$, $Z_v(f,\chi_v|\cdot|_v^s)=P_f(q_v^{-s})\,(1-\chi(\mathfrak p_v)q_v^{-s})^{-1}$ with $P_f$ a Laurent polynomial (entire if $\chi$ is ramified at $v$)
-- statement:
--   **Local zeta integrals at a finite place are Laurent polynomials in $q_v^{-s}$ times the Euler factor** (Tate's local theory behind the Euler factors (6.3.1.4) of the source, including "$L_v(c_v)=1$ if $\chi$ is ramified at $v$").
--
--   Let $F$ be a number field, $\chi$ a Hecke character of $F$, $v$ a finite place with completion $F_v$, ring of integers $\mathcal O_{F_v}$, uniformizer $\pi_v$, residue cardinality $q_v=N(\mathfrak p_v)$, normalized absolute value $|\cdot|_v$ (so $|\pi_v|_v=q_v^{-1}$) and local multiplicative Tamagawa measure $\mu_v$ on $F_v^\times$ (the Haar measure with $\mu_v(\mathcal O_{F_v}^\times)=N(\mathfrak d_v)^{-1/2}$, where $\mathfrak d_v$ is the $\mathfrak p_v$-part of the different of $F/\mathbb Q$). Let $\chi_v$ be the local component of $\chi$ at $v$; $\chi$ is **unramified** at $v$ if $\chi_v$ is trivial on $\mathcal O_{F_v}^\times$, and **ramified** at $v$ otherwise. Let
--   $$L_v(s,\chi)=\bigl(1-\chi(\mathfrak p_v)\,q_v^{-s}\bigr)^{-1},\qquad \chi(\mathfrak p_v)=\begin{cases}\chi_v(\pi_v)&\chi\text{ unramified at }v,\\0&\chi\text{ ramified at }v,\end{cases}$$
--   be its local Euler factor (6.3.1.4): $L_v(s,\chi)=(1-q_v^{-s-it_v})^{-1}$ at unramified places (where $t_v\in\mathbb R$ is defined by $\chi(\mathfrak p_v)=q_v^{-it_v}$, see `MasulloGRH.localComponent_eq_norm_cpow_of_isUnramifiedAt`) and $L_v(s,\chi)=1$ at ramified places. For a Schwartz–Bruhat function $f\in\mathcal S(F_v)$ (locally constant with compact support) the local zeta integral is
--   $$Z_v(f,\chi_v|\cdot|_v^s)=\int_{F_v^\times}f(x)\,\chi_v(x)\,|x|_v^s\,d\mu_v(x),\qquad\operatorname{Re}s>0 .$$
--
--   Then for every $f\in\mathcal S(F_v)$ there is a Laurent polynomial $P_f(X)=\sum_{n\in\mathbb Z}c_nX^n\in\mathbb C[X,X^{-1}]$ such that for every $s$ with $\operatorname{Re}s>0$ the integral converges absolutely and
--   $$Z_v(f,\chi_v|\cdot|_v^s)=P_f\bigl(q_v^{-s}\bigr)\,L_v(s,\chi).$$
--
--   In particular $Z_v(f,\chi_v|\cdot|_v^s)/L_v(s,\chi)$ extends to an entire function of $s$ (periodic with period $2\pi i/\log q_v$), and at a ramified place every local zeta integral is itself entire; this is the sense in which $L_v(s,\chi)$ is the Euler factor of $L(s,\chi)$ at $v$ (together with the converse statement `MasulloGRH.exists_finiteLocalZeta_eq_laurent_mul_eulerFactor`, $L_v$ is the generator of the fractional ideal of $\mathbb C[q_v^{s},q_v^{-s}]$ spanned by the local zeta integrals). The source uses the ramified case in the proof of Theorem 6.2.2.1(1) ("as meromorphic (in fact entire) functions", p. 301) and the Euler factors in the global converse theorems of §6.3.2.
--
--   **Formalization Note.** The Laurent polynomial is a finitely supported family $c:\mathbb Z\to_0\mathbb C$, evaluated as $\sum_nc_n(q_v^{-s})^n$. $\chi_v$, $\chi(\mathfrak p_v)$ and $\mu_v$ are `HeckeCharacter.localComponent`, `HeckeCharacter.primeValue` and `MasulloGRH.finiteLocalMulTamagawa`; $\mathcal S(F_v)$ is encoded by `IsLocallyConstant f ∧ HasCompactSupport f`, and $|x|_v$ is the norm of `v.adicCompletion F` ($|\pi_v|=q_v^{-1}$). The factor $(1-\chi(\mathfrak p_v)q_v^{-s})^{-1}$ is exactly the factor at $v$ of the platform's Euler product `MasulloGRH.heckeEulerProduct`; it is finite and nonzero for $\operatorname{Re}s>0$ since $|\chi(\mathfrak p_v)|\le1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 303, §6.3.1, eq. (6.3.1.4) (Euler factors $L_v(c_v)$, $=1$ at ramified places); pp. 301–302, proof of Theorem 6.2.2.1(1) (ramified local zeta integrals are entire)

import Mathlib
import Definitions.Def_MasulloGRH_HeckeLFunction
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem finiteLocalZeta_eq_laurent_mul_eulerFactor
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (f : v.adicCompletion F → ℂ) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ c : ℤ →₀ ℂ, ∀ s : ℂ, 0 < s.re →
      Integrable
        (fun x : (v.adicCompletion F)ˣ =>
          f (x : v.adicCompletion F) * χ.localComponent v x *
            ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s)
        (finiteLocalMulTamagawa F v) ∧
      ∫ x : (v.adicCompletion F)ˣ,
        f (x : v.adicCompletion F) * χ.localComponent v x *
          ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s ∂(finiteLocalMulTamagawa F v) =
        (c.sum fun n a => a * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) ^ n) *
          (1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by sorry

end MasulloGRH
