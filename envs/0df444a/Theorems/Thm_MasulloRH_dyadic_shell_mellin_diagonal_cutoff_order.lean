-- Prove2me | Theorems.Thm_MasulloRH_dyadic_shell_mellin_diagonal_cutoff_order
-- name    : MasulloRH.dyadic_shell_mellin_diagonal_cutoff_order
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T02:15:40.382349+00:00
-- url     : https://prove2.me/theorems/5fc0c830-37ff-4e9c-91c9-a9a3cf4c6b17
-- title:
--   Noncommuting cutoff limits for a radial convolution on the dyadic shell diagonal
-- statement:
--   Let $T_kf(x)=\int_0^\infty k(r)f(x/r)\,dr/r$. For measurable $k,f$ with absolutely convergent Mellin integrals at $a\in\mathbb R$, pairing $T_kf$ against a measurable $w$ satisfying $|w(x)|\le Cx^a$ under $dx/x$ equals pairing $f(u)$ against $\int k(r)w(ru)\,dr/r$.
--
--   There are smooth, compactly supported real functions $\psi,g,k$ with $\int_0^\infty\psi=0$, $g(x)=\sum_{j\ge1}\psi(2^jx)$ for $x>0$, and $\operatorname{supp}k\subset[1,2]$, with the following property. Form $F(t)=\sum_{n\ge1}\psi(nt)$ and use inclusion–exclusion over the odd primes up to $B$ to form the corrected even shell $G_B(t)=\sum_{U}(-1)^{|U|}F(2\prod_{q\in U}q\,t)$. Set $D_j(v)=\int_{1/(j+1)}^{j+1} x^{-1/2}T_kv(x)\,dx$. For each fixed $j$, $D_j(G_B)$ eventually equals $D_j(g)$. All convolved half-Mellin integrals are absolutely convergent and satisfy the product formula. The two orders of limits give
--   $$\lim_{j\to\infty}\lim_{B\to\infty}D_j(G_B)=M_{1/2}(k)M_{1/2}(g)\ne0,\qquad \lim_{B\to\infty}\lim_{j\to\infty}D_j(G_B)=0.$$
-- source:
--   Radial rank-one test for the two-variable cutoff step in Masullo, The Music of the Primes, Chapters 11–12. Uses the accepted smooth compact dyadic shell theorem (1d740792-b9e7-4ef3-bb42-6512e73025f5). Related native convolution identities include MellinConvolutionTransform (7ed4b175-4b88-4233-a006-83e8a4c23e61) and the Langlands–Tunnell Mellin convolution theorem (e2ed40a3-a382-5c4c-aea8-47ccde557bfe).

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Data.Nat.Prime.Basic

open Set Filter Finset MeasureTheory
open scoped Topology

theorem MasulloRH.dyadic_shell_mellin_diagonal_cutoff_order :
    (∀ (k f w : ℝ → ℂ) (a C : ℝ), Measurable k → Measurable f → Measurable w →
      MellinConvergent k (a:ℂ) → MellinConvergent f (a:ℂ) →
      (∀ t : ℝ, 0 < t → ‖w t‖ ≤ C * t^a) →
      (∫ x in Ioi (0:ℝ), (w x / (x:ℂ)) *
        (∫ r in Ioi (0:ℝ), (k r / (r:ℂ)) * f (x/r))) =
      ∫ u in Ioi (0:ℝ), (f u / (u:ℂ)) *
        (∫ r in Ioi (0:ℝ), (k r / (r:ℂ)) * w (r*u))) ∧
    ∃ ψ g k : ℝ → ℝ,
      let s : ℂ := 1/2
      let F (t : ℝ) : ℂ := ∑' n : ℕ, (ψ (((n:ℝ)+1)*t) : ℂ)
      let Q (B : ℕ) := (range (B+1)).filter (fun l : ℕ => l.Prime ∧ l ≠ 2)
      let G (B : ℕ) (t : ℝ) := ∑ U ∈ (Q B).powerset,
        (-1:ℂ)^U.card * F ((2*∏ l ∈ U, (l:ℝ))*t)
      let T (v : ℝ → ℂ) (x : ℝ) := ∫ r in Ioi (0:ℝ), ((k r:ℂ)/(r:ℂ))*v (x/r)
      let D (v : ℝ → ℂ) (j : ℕ) := ∫ x in Ioo (1/((j:ℝ)+1)) ((j:ℝ)+1),
        (x:ℂ)^(s-1) * T v x
      let gC (t : ℝ) : ℂ := g t
      let c := mellin (fun t : ℝ => (k t:ℂ)) s * mellin gC s
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      (∀ t : ℝ, t ≤ 0 ∨ 8 ≤ t → ψ t = 0) ∧ (∫ t in Ioi (0:ℝ), ψ t) = 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      (∀ t : ℝ, 0 < t → (∑' j : ℕ, (ψ (2^(j+1)*t):ℂ)) = gC t) ∧
      ContDiff ℝ (⊤ : ℕ∞) k ∧ tsupport k ⊆ Icc 1 2 ∧
      (∀ B : ℕ, HasMellin (T (G B)) s
        (mellin (fun t : ℝ => (k t:ℂ)) s * mellin (G B) s)) ∧
      HasMellin (T gC) s c ∧ c ≠ 0 ∧
      (∀ j : ℕ, ∀ᶠ B : ℕ in atTop, D (G B) j = D gC j) ∧
      Tendsto (D gC) atTop (𝓝 c) ∧
      (∀ B : ℕ, Tendsto (D (G B)) atTop (𝓝 (mellin (T (G B)) s))) ∧
      Tendsto (fun B : ℕ => mellin (T (G B)) s) atTop (𝓝 0) := by sorry
