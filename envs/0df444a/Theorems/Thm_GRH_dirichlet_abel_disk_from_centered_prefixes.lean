-- Prove2me | Theorems.Thm_GRH_dirichlet_abel_disk_from_centered_prefixes
-- name    : GRH.dirichlet_abel_disk_from_centered_prefixes
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T15:34:09.808514+00:00
-- url     : https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2
-- title:
--   An Abel summation bound from a disk containing the character prefixes
-- statement:
--   Let $A_n=\sum_{k=1}^n\chi(k)$ be the prefixes of a nonprincipal Dirichlet character and $P_M(s)=\sum_{k=1}^M\chi(k)k^{-s}$. Suppose $|A_n-c|\le R$ for every $n\ge M$. For $x=\Re s>0$, the distance from $L(s,\chi)$ to $P_M(s)+(c-A_M)(M+1)^{-s}$ is at most $R(|s|/x)(M+1)^{-x}$.
-- source:
--   Developed for the centered Möbius bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive grid condition at https://prove2.me/theorems/a7f725ef-ecef-5ae2-855e-fc5b2d31cf0a. The centered-prefix estimate uses the published power variation bound at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965 and Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Data.Nat.Totient

theorem GRH.dirichlet_abel_disk_from_centered_prefixes (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (M : ℕ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hdisk : ∀ n : ℕ, M ≤ n → ‖(∑ k ∈ Finset.range n, χ ((k+1:ℕ):ZMod q)) - c‖ ≤ R)
    (s : ℂ) (hs : 0 < s.re) :
    ‖χ.LFunction s - ((∑ k ∈ Finset.range M, χ ((k+1:ℕ):ZMod q) * ((k+1:ℕ):ℂ)^(-s)) +
       (c - ∑ k ∈ Finset.range M, χ ((k+1:ℕ):ZMod q)) * ((M+1:ℕ):ℂ)^(-s))‖
      ≤ R*(‖s‖/s.re)*((M:ℝ)+1)^(-s.re) := by sorry
