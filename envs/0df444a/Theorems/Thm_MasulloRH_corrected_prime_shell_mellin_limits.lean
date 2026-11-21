-- Prove2me | Theorems.Thm_MasulloRH_corrected_prime_shell_mellin_limits
-- name    : MasulloRH.corrected_prime_shell_mellin_limits
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T01:31:19.65972+00:00
-- url     : https://prove2.me/theorems/6e438335-bf6f-44ab-b3d2-ee04d67ae833
-- title:
--   Mellin limits for a finitely sieved scalar shell and the pure prime-power shell
-- statement:
--   Fix a prime $p$ and $0<a\le1$. Let $\psi$ be complex valued, with $M_a(\psi)$ absolutely convergent. Suppose $F(t)=\sum_{n\ge1}\psi(nt)$ is absolutely summable at each $t>0$ and $M_a(F)$ converges absolutely. Let $Q_B$ contain the primes up to $B$ except $p$, and put
--   $$G_B(t)=\sum_{U\subseteq Q_B}(-1)^{|U|}F\bigl(p\prod_{\ell\in U}\ell\,t\bigr).$$
--   Then $M_a(G_B)=p^{-a}M_a(F)\prod_{\ell\in Q_B}(1-\ell^{-a})$ tends to zero. The pure prime-power sum $P(t)=\sum_{j\ge1}\psi(p^jt)$ has absolutely convergent Mellin integral $M_a(P)=M_a(\psi)/(p^a-1)$. Consequently $M_a(G_B)$ does not tend to $M_a(P)$ whenever $M_a(\psi)\ne0$.
-- source:
--   Finite scalar model for the rational prime shell in Masullo, The Music of the Primes, §11.3, equations (11.3.1.1–5); Mellin dilation, Euler’s divergence of prime reciprocals, and absolute convergence of a geometric series of dilates. Related discussion: https://github.com/mccorvie/riemann-masullo/issues/1358.

import Mathlib.Analysis.MellinTransform
import Mathlib.Data.Nat.Prime.Basic

open Finset Filter
open scoped Topology

theorem MasulloRH.corrected_prime_shell_mellin_limits (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1)
    (ψ : ℝ → ℂ) (hψ : MellinConvergent ψ (a:ℂ))
    (hF : (∀ t : ℝ, 0 < t → Summable (fun n : ℕ => ψ (((n:ℝ)+1)*t))) ∧
      MellinConvergent (fun t : ℝ => ∑' n : ℕ, ψ (((n:ℝ)+1)*t)) (a:ℂ)) :
    let F (t : ℝ) := ∑' n : ℕ, ψ (((n:ℝ)+1)*t)
    let Q (B : ℕ) := (range (B+1)).filter (fun l : ℕ => l.Prime ∧ l ≠ p)
    let G (B : ℕ) (t : ℝ) := ∑ U ∈ (Q B).powerset,
      (-1:ℂ)^U.card * F (((p:ℝ)*∏ l ∈ U, (l:ℝ))*t)
    let shell (t : ℝ) := ∑' j : ℕ, ψ ((p:ℝ)^(j+1)*t)
    (∀ B : ℕ, HasMellin (G B) (a:ℂ)
      (((∏ l ∈ Q B, (1-(l:ℝ)^(-a)) : ℝ):ℂ) * ((((p:ℝ)^(-a):ℝ):ℂ) * mellin F (a:ℂ)))) ∧
    Tendsto (fun B : ℕ => mellin (G B) (a:ℂ)) atTop (𝓝 0) ∧
    HasMellin shell (a:ℂ) (mellin ψ (a:ℂ) / ((((p:ℝ)^a-1):ℝ):ℂ)) ∧
    (mellin ψ (a:ℂ) ≠ 0 → ¬Tendsto (fun B : ℕ => mellin (G B) (a:ℂ)) atTop
      (𝓝 (mellin shell (a:ℂ)))) := by sorry
