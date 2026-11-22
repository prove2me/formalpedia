-- Prove2me | Theorems.Thm_MasulloGRH_exists_finiteLocalZeta_eq_laurent_mul_eulerFactor
-- name    : MasulloGRH.exists_finiteLocalZeta_eq_laurent_mul_eulerFactor
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:35:11.43694+00:00
-- url     : https://prove2.me/theorems/82ba550b-cbb7-4f47-a4a0-5710a8dda005
-- title:
--   (6.3.1.4), Tate — every $P(q_v^{-s})\,(1-\chi(\mathfrak p_v)q_v^{-s})^{-1}$, $P$ a Laurent polynomial, is a local zeta integral $Z_v(f,\chi_v|\cdot|_v^s)$ with $f\in\mathcal S(F_v)$
-- statement:
--   **Every Laurent multiple of the local Euler factor is a local zeta integral** (Tate's local theory behind the Euler factors (6.3.1.4) of the source; converse of `MasulloGRH.finiteLocalZeta_eq_laurent_mul_eulerFactor`).
--
--   Let $F$ be a number field, $\chi$ a Hecke character of $F$, $v$ a finite place with completion $F_v$, ring of integers $\mathcal O_{F_v}$, uniformizer $\pi_v$, residue cardinality $q_v=N(\mathfrak p_v)$, normalized absolute value $|\cdot|_v$ (so $|\pi_v|_v=q_v^{-1}$) and local multiplicative Tamagawa measure $\mu_v$ on $F_v^\times$ (the Haar measure with $\mu_v(\mathcal O_{F_v}^\times)=N(\mathfrak d_v)^{-1/2}$, where $\mathfrak d_v$ is the $\mathfrak p_v$-part of the different of $F/\mathbb Q$). Let $\chi_v$ be the local component of $\chi$ at $v$; $\chi$ is **unramified** at $v$ if $\chi_v$ is trivial on $\mathcal O_{F_v}^\times$, and **ramified** at $v$ otherwise. Let
--   $$L_v(s,\chi)=\bigl(1-\chi(\mathfrak p_v)\,q_v^{-s}\bigr)^{-1},\qquad \chi(\mathfrak p_v)=\begin{cases}\chi_v(\pi_v)&\chi\text{ unramified at }v,\\0&\chi\text{ ramified at }v,\end{cases}$$
--   be its local Euler factor (6.3.1.4): $L_v(s,\chi)=(1-q_v^{-s-it_v})^{-1}$ at unramified places (where $t_v\in\mathbb R$ is defined by $\chi(\mathfrak p_v)=q_v^{-it_v}$, see `MasulloGRH.localComponent_eq_norm_cpow_of_isUnramifiedAt`) and $L_v(s,\chi)=1$ at ramified places. For a Schwartz–Bruhat function $f\in\mathcal S(F_v)$ (locally constant with compact support) the local zeta integral is
--   $$Z_v(f,\chi_v|\cdot|_v^s)=\int_{F_v^\times}f(x)\,\chi_v(x)\,|x|_v^s\,d\mu_v(x),\qquad\operatorname{Re}s>0 .$$
--
--   Then for every Laurent polynomial $P(X)=\sum_{n\in\mathbb Z}c_nX^n\in\mathbb C[X,X^{-1}]$ there is $f\in\mathcal S(F_v)$ such that for every $s$ with $\operatorname{Re}s>0$
--   $$Z_v(f,\chi_v|\cdot|_v^s)=P\bigl(q_v^{-s}\bigr)\,L_v(s,\chi).$$
--
--   Together with `MasulloGRH.finiteLocalZeta_eq_laurent_mul_eulerFactor` this says that the set of local zeta integrals $\{Z_v(f,\chi_v|\cdot|_v^s):f\in\mathcal S(F_v)\}$ is exactly $L_v(s,\chi)\,\mathbb C[q_v^{s},q_v^{-s}]$: the Euler factor $L_v(s,\chi)$ of (6.3.1.4) is the "g.c.d." of the local zeta integrals, equal to $1$ at the ramified places. In particular $L_v(s,\chi)$ itself (and, at ramified places, the constant $1$) is a local zeta integral. The converse theorems of §6.3.2 of the source likewise need test functions with prescribed (S-local) zeta integrals (p. 309, via its Theorem 5.4.1.1).
--
--   **Formalization Note.** Same encoding as in `MasulloGRH.finiteLocalZeta_eq_laurent_mul_eulerFactor`: $P$ is a finitely supported $c:\mathbb Z\to_0\mathbb C$ evaluated at $q_v^{-s}$; $\mathcal S(F_v)$ is `IsLocallyConstant f ∧ HasCompactSupport f`. Absolute convergence of the integrals for $\operatorname{Re}s>0$ is part of the companion statement and is not repeated.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 303, §6.3.1, eq. (6.3.1.4) (Euler factors $L_v(c_v)$, $=1$ at ramified places); pp. 301–302, proof of Theorem 6.2.2.1(1)

import Mathlib
import Definitions.Def_MasulloGRH_HeckeLFunction
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem exists_finiteLocalZeta_eq_laurent_mul_eulerFactor
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (c : ℤ →₀ ℂ) :
    ∃ f : v.adicCompletion F → ℂ, IsLocallyConstant f ∧ HasCompactSupport f ∧
      ∀ s : ℂ, 0 < s.re →
        ∫ x : (v.adicCompletion F)ˣ,
            f (x : v.adicCompletion F) * χ.localComponent v x *
              ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s ∂(finiteLocalMulTamagawa F v) =
          (c.sum fun n a => a * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) ^ n) *
            (1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by sorry

end MasulloGRH
