-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_eq_16
-- name    : HetExponomial.ChoiceProb.eq_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:51.836212+00:00
-- url     : https://prove2.me/theorems/12b89c2f-a7fd-42d5-abea-f8b9c1b901f6
-- title:
--   Proof of Theorem 1, display (16), p. 43 — the integral (1) splits into tail integrals over the distinct utility levels a_1 < … < a_k = u_i
-- statement:
--   In the HEC model with $n\ge 2$ and rates $\lambda_j>0$, let $a_1<a_2<\dots<a_l$ be the distinct values of the ideal utilities $u_1,\dots,u_n$. Fix a choice $i$ with $u_i=a_k$, and write $B(x)=\{j\in N: u_j\ge x\}$. For a level $a_w$ and a lower limit $c$ put
--   $$
--   T_w(c)=\int_c^\infty \exp\Big[-\sum_{j\in B(a_w)}\lambda_j\,(u_j-u_i+z)\Big]\,dz .
--   $$
--   Then the integral in (1) decomposes along the levels $a_k, a_{k-1},\dots,a_1$:
--   $$
--   \int_0^\infty \lambda_i\exp\Big[-\sum_{j\in N}\lambda_j(u_j-u_i+z)^+\Big]dz
--   =\lambda_i\Big\{\sum_{w=2}^{k}\big[T_w(a_k-a_w)-T_w(a_k-a_{w-1})\big]+T_1(a_k-a_1)\Big\}.
--   $$
--   The $w$-th summand is the line of display (16) that carries the set $B(a_w)$. For $w=k$ its first term is $T_k(0)$, since $a_k-a_k=0$, and the lowest level $w=1$ has no negative term.
--
--   This is display (16) in the proof of Theorem 1. It splits the integral (1) into pieces on which the positive parts disappear, so that each piece can be integrated explicitly.
--
--   **Formalization Note** The levels are `level u`, the increasing enumeration of the finite set of values of $u$, indexed from $0$. The paper's $a_w$ is `level u ⟨w-1, _⟩`, and the hypothesis `level u k = u i` pins $k$ (shifted by one) as the level of choice $i$. The summand for a Lean index $w$ subtracts the tail integral from $u_i-a_{w-1}$ only when $w>0$, that is, when the level is not the lowest. Each tail integral is a Bochner integral over $(c,\infty)$. Its integrand is integrable because $i\in B(a_w)$ for $a_w\le u_i$.
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 43, proof of Theorem 1, display (16)

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

namespace HetExponomial.ChoiceProb

theorem eq_16 {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n)
    (k : Fin (levels u).card) (hk : level u k = u i) :
    ∫ z in Set.Ioi 0, lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) =
      lam i * ∑ w ∈ Finset.univ.filter (fun w => w ≤ k),
        (tailInt u lam i (level u w) (u i - level u w) -
          if 0 < w.val then
            tailInt u lam i (level u w)
              (u i - level u ⟨w.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) w.isLt⟩)
          else 0) := by sorry

end HetExponomial.ChoiceProb
