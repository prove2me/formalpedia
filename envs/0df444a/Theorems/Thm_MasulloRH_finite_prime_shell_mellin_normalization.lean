-- Prove2me | Theorems.Thm_MasulloRH_finite_prime_shell_mellin_normalization
-- name    : MasulloRH.finite_prime_shell_mellin_normalization
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T01:44:18.477632+00:00
-- url     : https://prove2.me/theorems/c2c832e0-37f7-48a3-9a12-809625c31683
-- title:
--   Exact finite-cutoff normalization of rational prime-shell Mellin moments
-- statement:
--   Let $p\le B$ be prime, $0<a<1$, and let $u$ be a real twice continuously differentiable compactly supported positive-half-line test, vanishing near zero, with $\int u(t)\,dt=0$. Write $M_a$ for the Mellin transform with weight $t^a\,dt/t$. Let $G_{B,p}$ be the finite inclusion–exclusion sieve of the ordinary positive integer periodization, selecting multiples of $p$ and excluding all other primes up to $B$. Then $W_B(a)=\zeta(a)\prod_{\ell\le B,\;\ell\ {\rm prime}}(1-\ell^{-a})$ is nonzero, and $M_a(G_{B,p})/W_B(a)=M_a(u)/(p^a-1)$. This single prime-independent normalization recovers the pure prime-power Mellin value at every finite cutoff, including at $a=1/2$. The statement concerns the rational scalar shell before the geometric trace comparison.
-- source:
--   Classical Müntz formula, e.g. J.-F. Burnol, equation (5), https://www.emis.de/journals/JTNB/2004-1/Burnol.pdf. Application to Masullo’s proposed cutoff repair in https://github.com/mccorvie/riemann-masullo/issues/1358#issuecomment-7055141128. Uses the accepted finite Mellin product https://prove2.me/theorems/6e438335-bf6f-44ab-b3d2-ee04d67ae833 and the independently proved small-height nonvanishing theorem https://prove2.me/theorems/d752be9a-a1b7-4d46-b0b7-8e2125373a4e.

import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Nat.Prime.Basic

open Finset Set Filter MeasureTheory Asymptotics
open scoped Topology

theorem MasulloRH.finite_prime_shell_mellin_normalization
    (p B : ℕ) (hp : p.Prime) (hpB : p ≤ B) (a : ℝ) (ha : 0 < a) (ha₁ : a < 1)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hsupp : ∀ x : ℝ, x ≤ r ∨ R ≤ x → u x = 0)
    (hmean : (∫ x in Ioi (0:ℝ), u x) = 0) :
    let ψ : ℝ → ℂ := fun t => (u t : ℂ)
    let F (t : ℝ) := ∑' n : ℕ, ψ (((n:ℝ)+1)*t)
    let Q := (range (B+1)).filter (fun l : ℕ => l.Prime ∧ l ≠ p)
    let G (t : ℝ) := ∑ U ∈ Q.powerset,
      (-1:ℂ)^U.card * F (((p:ℝ)*∏ l ∈ U, (l:ℝ))*t)
    let W : ℂ := riemannZeta (a:ℂ) * (((∏ l ∈ (range (B+1)).filter Nat.Prime,
      (1-(l:ℝ)^(-a)) : ℝ):ℂ))
    W ≠ 0 ∧ mellin G (a:ℂ) / W = mellin ψ (a:ℂ) / (((p:ℝ)^a-1 : ℝ):ℂ) := by sorry
