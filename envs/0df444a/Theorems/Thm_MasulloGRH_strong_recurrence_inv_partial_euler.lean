-- Prove2me | Theorems.Thm_MasulloGRH_strong_recurrence_inv_partial_euler
-- name    : MasulloGRH.strong_recurrence_inv_partial_euler
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:43:35.91518+00:00
-- url     : https://prove2.me/theorems/c6260830-fed9-4414-a040-b95507162742
-- title:
--   Proposition B.5.3.3 — strong recurrence of reciprocal partial Euler products
-- statement:
--   Let $F$ be a number field and $\chi\colon C_F\to U(1)$ a Hecke character. For a finite place $v$ let $\mathfrak p_v$ be its prime ideal, $q_v=N(\mathfrak p_v)$ its norm, and $\chi(\mathfrak p_v)=\chi_v(\pi_v)$ the value of $\chi$ at a uniformizer if $\chi$ is unramified at $v$ (and $0$ otherwise). $L_f(s,\chi)$ is the finite Hecke $L$-function, continued meromorphically to $\mathbb C$.
--
--   Let $S$ be a finite set of finite places of $F$ at which $\chi$ is unramified, and put
--   $$P_S(s)=\prod_{v\in S}L_v(\chi_v|\cdot|_v^{s})^{-1}=\prod_{v\in S}\big(1-\chi(\mathfrak p_v)\,q_v^{-s}\big).$$
--   Let $a<0<b$ be real numbers and let $K$ be a compact subset of the open strip $\mathbb C_{(a,b)}$ with non-empty interior. Then for every $\varepsilon>0$ both sets
--   $$\Big\{t\ge0:\ \sup_{s\in K}|P_S(s+it)-P_S(s)|<\varepsilon\Big\},\qquad\Big\{t\le0:\ \sup_{s\in K}|P_S(s+it)-P_S(s)|<\varepsilon\Big\}$$
--   have positive **upper density**, where the upper density of $X\subset\mathbb R$ is $\limsup_{T\to+\infty}\lambda([-T,T]\cap X)/(2T)$.
--
--   This is a self-approximation property under vertical translation, in the sense of Bagchi, of the finite product of reciprocal Euler factors.
--
--   **Formalization Note** An open non-empty bounded interval containing $0$ is written $(a,b)$ with $a<0<b$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.5.3.2, Proposition B.5.3.3 (Strong recurrence of reciprocal partial Euler products), eqs. (B.5.3.4)–(B.5.3.5), pp. 632–633; upper density: Definition B.5.3.1(1)

import Definitions.Def_MasulloGRH_IdeleNorm
import Definitions.Def_MasulloGRH_MellinRpos

set_option autoImplicit false

namespace MasulloGRH

open NumberField IsDedekindDomain

theorem strong_recurrence_inv_partial_euler
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : HeckeCharacter F) (hχ : ∀ v ∈ S, χ.IsUnramifiedAt v)
    (a b : ℝ) (ha : a < 0) (hb : 0 < b)
    (K : Set ℂ) (hK : IsCompact K) (hKI : K ⊆ openStrip a b) (hKint : (interior K).Nonempty)
    (ε : ℝ) (hε : 0 < ε) :
    0 < upperDensity {t : ℝ | 0 ≤ t ∧
      sSup ((fun s : ℂ => ‖∏ v ∈ S, eulerFactorInv χ v (s + t * Complex.I) -
        ∏ v ∈ S, eulerFactorInv χ v s‖) '' K) < ε} ∧
    0 < upperDensity {t : ℝ | t ≤ 0 ∧
      sSup ((fun s : ℂ => ‖∏ v ∈ S, eulerFactorInv χ v (s + t * Complex.I) -
        ∏ v ∈ S, eulerFactorInv χ v s‖) '' K) < ε} := by sorry

end MasulloGRH
