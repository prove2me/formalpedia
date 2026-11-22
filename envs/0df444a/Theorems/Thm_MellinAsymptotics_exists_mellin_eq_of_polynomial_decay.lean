-- Prove2me | Theorems.Thm_MellinAsymptotics_exists_mellin_eq_of_polynomial_decay
-- name    : MellinAsymptotics.exists_mellin_eq_of_polynomial_decay
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:05.295483+00:00
-- url     : https://prove2.me/theorems/5b599ee6-d03d-4f49-be03-e00a1aedc8e2
-- title:
--   Mellin inversion on a strip: a holomorphic function with $|s|^N|f(s)|$ bounded, $N>2$, is a Mellin transform
-- statement:
--   **Mellin inversion on a vertical strip under polynomial decay.** Let $a\in\mathbb R$ and $b\in\mathbb R\cup\{+\infty\}$ with $a<b$, and let $N>2$ be a real number. Let $f$ be a holomorphic function on the strip $\mathbf C_{(a,b)}=\{s\in\mathbb C:a<\operatorname{Re}(s)<b\}$ such that $|s|^N|f(s)|$ is bounded on every closed strip $\{c\le\operatorname{Re}(s)\le d\}$ with $a<c\le d<b$. Then for every integer $m$ with $0\le m<N-1$ there is a function $\varphi\in C^m(\mathbb R_{>0})$ with the following properties.
--
--   1. For every $\sigma\in(a,b)$ the function $t^\sigma\varphi(t)$ belongs to $C_0^m(\mathbb R_{>0})$: in the logarithmic variable, $F_\sigma(x):=e^{\sigma x}\varphi(e^x)$ is of class $C^m$ on $\mathbb R$ and $F_\sigma^{(j)}(x)\to0$ as $|x|\to\infty$ for every $0\le j\le m$.
--   2. For every $\sigma\in(a,b)$ the function $t^\sigma\varphi(t)$ belongs to $L^2(\mathbb R_{>0},\mathrm dt/t)$, i.e. $F_\sigma\in L^2(\mathbb R,\mathrm dx)$.
--   3. For every $s\in\mathbf C_{(a,b)}$ the Mellin integral of $\varphi$ converges absolutely and
--   $$M(\varphi)(s)=\int_0^\infty\varphi(t)\,t^{s}\,\frac{\mathrm dt}{t}=f(s).$$
--
--   This is the converse direction of Mellin inversion: holomorphic functions on a strip with enough decay along vertical lines are Mellin transforms, with regularity of $\varphi$ governed by the rate of decay. It is Proposition B.2.1.8 of the source, stated there as a partial converse to its theorem relating asymptotic expansions of $\varphi$ and poles of $M(\varphi)$.
--
--   **Deviation from the source.** The source assumes $a>0$; this is not used and is omitted. The space $C_0^m(\mathbb R_{>0})$ of (B.2.1.19) is unfolded in the logarithmic variable $x=\log t$ as in items 1 and 2.
--
--   **Formalization Note.** `mellin φ s` and `MellinConvergent φ s` are Mathlib's Mellin transform $\int_0^\infty t^{s-1}\varphi(t)\,\mathrm dt$ and its absolute convergence; $\varphi$ is a function `ℝ → ℂ` of which only the values on $(0,\infty)$ matter, and $\varphi\in C^m(\mathbb R_{>0})$ is `ContDiffOn ℝ m φ (Set.Ioi 0)`. The right end $b$ is an element of `WithTop ℝ`. The boundedness hypothesis is `‖s‖ ^ N * ‖f s‖ ≤ C` on each closed strip, with a real power. Vanishing at infinity is convergence to $0$ along the cocompact filter of $\mathbb R$, and derivatives are `iteratedDeriv`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 597, Proposition B.2.1.8 (Asymptotic Expansions and Mellin Inversion - II) and (B.2.1.19), with its proof on pp. 597-598

import Mathlib

open MeasureTheory Filter Topology Asymptotics

set_option autoImplicit false

namespace MellinAsymptotics

theorem exists_mellin_eq_of_polynomial_decay
    (a : ℝ) (b : WithTop ℝ) (hab : (a : WithTop ℝ) < b) (N : ℝ) (hN : 2 < N) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {s : ℂ | a < s.re ∧ (s.re : WithTop ℝ) < b})
    (hbd : ∀ c d : ℝ, a < c → c ≤ d → (d : WithTop ℝ) < b →
      ∃ C : ℝ, ∀ s : ℂ, c ≤ s.re → s.re ≤ d → ‖s‖ ^ N * ‖f s‖ ≤ C)
    (m : ℕ) (hm : (m : ℝ) < N - 1) :
    ∃ φ : ℝ → ℂ, ContDiffOn ℝ m φ (Set.Ioi 0) ∧
      (∀ σ : ℝ, a < σ → (σ : WithTop ℝ) < b →
        ContDiff ℝ m (fun x : ℝ => (Real.exp (σ * x) : ℂ) * φ (Real.exp x)) ∧
        (∀ j : ℕ, j ≤ m → Tendsto
          (iteratedDeriv j (fun x : ℝ => (Real.exp (σ * x) : ℂ) * φ (Real.exp x)))
          (cocompact ℝ) (𝓝 0)) ∧
        MemLp (fun x : ℝ => (Real.exp (σ * x) : ℂ) * φ (Real.exp x)) 2 volume) ∧
      ∀ s : ℂ, a < s.re → (s.re : WithTop ℝ) < b → MellinConvergent φ s ∧ mellin φ s = f s := by sorry

end MellinAsymptotics
