-- Prove2me | Theorems.Thm_MellinAsymptotics_mellin_eq_holomorphic_add_principalParts
-- name    : MellinAsymptotics.mellin_eq_holomorphic_add_principalParts
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:04.491447+00:00
-- url     : https://prove2.me/theorems/0351021b-5de9-4c83-b557-92c0b6f91008
-- title:
--   Mellin transform and asymptotic expansion at $0$: meromorphic continuation to a wider strip with explicit principal parts
-- statement:
--   **Mellin transforms and asymptotic expansions at $0$.** Let $\varphi\colon(0,\infty)\to\mathbb C$ and let
--
--   $$M(\varphi)(s)=\int_0^\infty\varphi(t)\,t^{s}\,\frac{\mathrm dt}{t}$$
--
--   be its Mellin transform. Let $a\in\mathbb R$ and $b\in\mathbb R\cup\{+\infty\}$ with $a<b$, and assume that the Mellin integral converges absolutely for every $s$ in the strip $a<\operatorname{Re}(s)<b$. Let $\Sigma\subset\mathbb C$ be a finite set, and for each $\alpha\in\Sigma$ let $m_\alpha\ge0$ be an integer and $c_{\alpha,k}\in\mathbb C$ ($0\le k<m_\alpha$) be coefficients. Let $A\in\mathbb R$ be such that $A<\operatorname{Re}(-\alpha)\le a$ for all $\alpha\in\Sigma$, and assume the asymptotic expansion
--
--   $$\varphi(t)-\sum_{\alpha\in\Sigma}\ \sum_{0\le k<m_\alpha}c_{\alpha,k}\,t^{\alpha}(\log t)^{k}=O\bigl(t^{-A}\bigr)\qquad(t\to0^+).$$
--
--   Then there is a function $g$, holomorphic on the wider strip $A<\operatorname{Re}(s)<b$, such that for all $s$ with $a<\operatorname{Re}(s)<b$
--
--   $$M(\varphi)(s)=g(s)+\sum_{\alpha\in\Sigma}\ \sum_{0\le k<m_\alpha}\frac{(-1)^k\,k!\;c_{\alpha,k}}{(s+\alpha)^{k+1}} .$$
--
--   In particular $M(\varphi)$ extends to a meromorphic function on $A<\operatorname{Re}(s)<b$ whose only possible poles are the points $-\alpha$, $\alpha\in\Sigma$, with the displayed principal parts; if $m_\alpha\ge1$ and $c_{\alpha,m_\alpha-1}\ne0$, the pole at $-\alpha$ has order exactly $m_\alpha$.
--
--   For example, for $\varphi(t)=e^{-t}$ one has $a=0$, $b=+\infty$, and the expansion $e^{-t}=\sum_{j\le n}(-1)^jt^j/j!+O(t^{n+1})$ gives the continuation of $\Gamma(s)$ to $\operatorname{Re}(s)>-n-1$ with simple poles at $s=-j$ of residue $(-1)^j/j!$.
--
--   This is the basic dictionary between the asymptotic behaviour of a function at $0$ and the poles of its Mellin transform. It is Theorem B.2.1.7(2) of the source, in its complements on the Mellin transform (§B.2.1.2).
--
--   **Deviation from the source.** The source indexes the logarithmic powers by $1\le k\le m_\alpha$ with $(\log t)^{k-1}$; here $k$ is shifted by one. The source assumes moreover that $\varphi$ is smooth with $t^\sigma\varphi$ of Schwartz type on $\mathbb R_{>0}$ for $\sigma\in(a,b)$, that $a>0$, $A<0$, $m_\alpha\ge1$ and that the top coefficients are non-zero; only the absolute convergence of the Mellin integral on the strip is used, and the conclusion is the explicit decomposition obtained in the source's proof (the displayed formula for $g(s)$ on p. 597), which contains the source's conclusion about the poles and their orders.
--
--   **Formalization Note.** `mellin φ s` and `MellinConvergent φ s` are Mathlib's Mellin transform $\int_0^\infty t^{s-1}\varphi(t)\,\mathrm dt$ and its absolute convergence; $\varphi$ is a function `ℝ → ℂ` of which only the values on $(0,\infty)$ matter. The right end $b$ is an element of `WithTop ℝ`. The power $t^\alpha$ is the complex power `(t : ℂ) ^ α` $=e^{\alpha\log t}$ for $t>0$, the expansion is an `IsBigO` along `𝓝[>] 0` against the real power $t^{-A}$, and "holomorphic" is `DifferentiableOn ℂ` on the open strip.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 595-597, Theorem B.2.1.7(2), (B.2.1.15), with its proof ((B.2.1.17), (B.2.1.18) and the displayed formula for $g(s)$) on pp. 596-597; the paper's footnote 9 mentions R. A. Handelsman and J. S. Lew, Asymptotic Expansion of a Class of Integral Transforms via Mellin Transforms, Arch. Rational Mech. Anal. 35 (1969), pp. 382-396, §2, as the reference originally given

import Mathlib

open MeasureTheory Filter Topology Asymptotics

set_option autoImplicit false

namespace MellinAsymptotics

theorem mellin_eq_holomorphic_add_principalParts
    (φ : ℝ → ℂ) (a A : ℝ) (b : WithTop ℝ) (hab : (a : WithTop ℝ) < b)
    (hφ : ∀ s : ℂ, a < s.re → (s.re : WithTop ℝ) < b → MellinConvergent φ s)
    (S : Finset ℂ) (m : ℂ → ℕ) (c : ℂ → ℕ → ℂ)
    (hS : ∀ α ∈ S, A < (-α).re ∧ (-α).re ≤ a)
    (hexp : (fun t : ℝ => φ t - ∑ α ∈ S, ∑ k ∈ Finset.range (m α),
        c α k * (t : ℂ) ^ α * (Real.log t : ℂ) ^ k) =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-A)) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s : ℂ | A < s.re ∧ (s.re : WithTop ℝ) < b} ∧
      ∀ s : ℂ, a < s.re → (s.re : WithTop ℝ) < b →
        mellin φ s = g s + ∑ α ∈ S, ∑ k ∈ Finset.range (m α),
          c α k * (-1) ^ k * (k.factorial : ℂ) / (s + α) ^ (k + 1) := by sorry

end MellinAsymptotics
