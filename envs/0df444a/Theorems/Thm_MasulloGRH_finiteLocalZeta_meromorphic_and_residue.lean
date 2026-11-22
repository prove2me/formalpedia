-- Prove2me | Theorems.Thm_MasulloGRH_finiteLocalZeta_meromorphic_and_residue
-- name    : MasulloGRH.finiteLocalZeta_meromorphic_and_residue
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:42.160807+00:00
-- url     : https://prove2.me/theorems/90c29d31-58ff-42f4-84c7-050bfbcc49b7
-- title:
--   Lemma 3.3.2.2, corrected — at a finite place $Z_v(f,|\cdot|_v^s)$ is meromorphic with at most a simple pole at $s=0$, of residue $N(\mathfrak d_v)^{-1/2}f(0)/\log q_v$
-- statement:
--   **Poles and residue of the local zeta integrals at a non-archimedean place** (Lemma 3.3.2.2 of the source, with the corrected residue).
--
--   Let $F$ be a number field, $v$ a finite place, $F_v$ the completion, $q_v=N(\mathfrak p_v)$ the cardinality of the residue field, $|\cdot|_v$ the normalized absolute value ($|\pi_v|_v=q_v^{-1}$), and $\mu_v$ the local multiplicative Tamagawa measure on $F_v^\times$, for which $\mu_v(\mathcal O_{F_v}^\times)=N(\mathfrak d_v)^{-1/2}$ with $\mathfrak d_v$ the local different. Let $f\in\mathcal S(F_v)$, i.e. $f:F_v\to\mathbb C$ is locally constant with compact support.
--
--   Then there is a meromorphic function $M$ on $\mathbb C$ such that:
--
--   1. for $\operatorname{Re}s>0$ the function $x\mapsto f(x)|x|_v^s$ is $\mu_v$-integrable on $F_v^\times$ and
--   $$M(s)=Z_v(f,|\cdot|_v^s)=\int_{F_v^\times}f(x)\,|x|_v^s\,d\mu_v(x);$$
--   2. $M$ is holomorphic at every $s$ with $q_v^{-s}\ne1$;
--   3. at $s=0$ it has at most a simple pole, with
--   $$\lim_{s\to0}s\,M(s)=N(\mathfrak d_v)^{-1/2}\,\frac{f(0)}{\log q_v}.$$
--
--   The points with $q_v^{-s}=1$ are the points $s\in\frac{2\pi i}{\log q_v}\mathbb Z$, all of which represent the trivial quasi-character $c=1$ of $F_v^\times$: on the cylinder $\Omega(F_v^\times)(1)=\mathbb C/\frac{2\pi i}{\log q_v}\mathbb Z$ the function $Z_v(f,\cdot)$ has at most one pole, a simple pole at $c=1$ (present iff $f(0)\neq0$). The source uses this local information to locate the poles of the $S$-local $Z$-functions (the divisor of $L_S$).
--
--   **Deviation from the source.** Equation (3.3.2.23) gives the residue as $N(\mathfrak d_{F_v/\mathbb Q_p})^{-1/2}\frac{1-q_v^{-1}}{\log q_v}\,\widehat f(0)$. This is not correct: for $f=1_{\mathcal O_{F_v}^\times}$ the zeta integral is the constant $\mu_v(\mathcal O_{F_v}^\times)$ and has no pole, although $\widehat f(0)\neq0$. The residue is $\mu_v(\mathcal O_{F_v}^\times)\,f(0)/\log q_v$, as stated here: near $0$ the function $f$ is constant on some $\pi_v^n\mathcal O_{F_v}$, whose contribution is $\mu_v(\mathcal O_{F_v}^\times)f(0)\,q_v^{-ns}/(1-q_v^{-s})$.
--
--   **Formalization Note.** $|x|_v$ is the norm of the completion `v.adicCompletion F`; the residue is expressed by the limit of $s\,M(s)$ as $s\to0$, $s\neq0$; $N(\mathfrak d_v)=N(\mathfrak p_v)^{m_v}$ with $m_v$ the multiplicity of $\mathfrak p_v$ in the different of $F/\mathbb Q$. Only the unramified component $c=|\cdot|_v^s$ is treated; on ramified components the zeta integral is entire.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 141, Lemma 3.3.2.2, eq. (3.3.2.23) (residue corrected); classical references cited in the proof: J. W. S. Cassels, A. Fröhlich (eds.), Algebraic Number Theory, Ch. XV (J. T. Tate, Fourier analysis in number fields and Hecke's zeta-functions), §2.4, Theorem 2.4.1, p. 315, and §2.5, p. 322

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem finiteLocalZeta_meromorphic_and_residue
    (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (f : v.adicCompletion F → ℂ) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ M : ℂ → ℂ, MeromorphicOn M Set.univ ∧
      (∀ s : ℂ, 0 < s.re →
        Integrable
          (fun x : (v.adicCompletion F)ˣ =>
            f (x : v.adicCompletion F) * ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s)
          (finiteLocalMulTamagawa F v) ∧
        M s = ∫ x : (v.adicCompletion F)ˣ,
          f (x : v.adicCompletion F) * ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s
            ∂(finiteLocalMulTamagawa F v)) ∧
      (∀ s : ℂ, ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 1 → AnalyticAt ℂ M s) ∧
      Filter.Tendsto (fun s : ℂ => s * M s) (nhdsWithin 0 {0}ᶜ)
        (nhds ((((Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
          multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))⁻¹ : ℝ) : ℂ) * f 0 /
            ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ))) := by sorry

end MasulloGRH
