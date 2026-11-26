-- Prove2me | Theorems.Thm_GRH_dirichlet_abel_bound_of_prefix_envelope
-- name    : GRH.dirichlet_abel_bound_of_prefix_envelope
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T17:21:56.935457+00:00
-- url     : https://prove2.me/theorems/efc35eb4-2c2f-5b4b-b14e-6c5d496affbf
-- title:
--   An Abel bound for a Dirichlet L-function from individual character-prefix bounds
-- statement:
--   Suppose $B(n)$ bounds the distance of the $n$th character partial sum from one, and $R$ bounds every $B(n)$. For $0<x\le\Re s$ and $K\ge|s|/x$, the distance of $L(s,\chi)$ from one is at most $K$ times the sum of $B(n)(n^{-x}-(n+1)^{-x})$ through the cutoff, plus $KR(M+1)^{-x}$.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/1b3886ba-6475-4979-b196-63418759603e. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Mathlib.NumberTheory.LSeries.DirichletContinuation

theorem GRH.dirichlet_abel_bound_of_prefix_envelope (Q M : ℕ) [NeZero Q] (ψ : DirichletCharacter ℂ Q) (hp : ψ ≠ 1)
    (s : ℂ) (x K R : ℝ) (B : ℕ → ℝ) (hx : 0 < x) (hxs : x ≤ s.re) (hK : ‖s‖/x ≤ K)
    (hR0 : 0 ≤ R) (hB0 : ∀ n, 0 ≤ B n)
    (hB : ∀ n : ℕ, ‖(∑ k ∈ Finset.range n,ψ ((k+1:ℕ):ZMod Q))-1‖ ≤ B n)
    (hR : ∀ n, B n ≤ R) :
    ‖ψ.LFunction s-1‖ ≤ K*((∑ k ∈ Finset.range M,B (k+1)*
      (((k:ℝ)+1)^(-x)-((k:ℝ)+2)^(-x)))+R*((M:ℝ)+1)^(-x)) := by sorry
