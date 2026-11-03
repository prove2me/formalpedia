-- Prove2me | Theorems.Thm_Grothendieck_ErInv_isInverse
-- name    : Grothendieck.ErInv_isInverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T15:04:52.116679+00:00
-- url     : https://prove2.me/theorems/8bf7d55b-4587-44c9-8b06-906bf0431143
-- title:
--   $E_r^{-1}$ is a two-sided inverse of $E_r$ on $[-1,1]$
-- statement:
--   For every integer $r\ge1$ and every $y\in[-1,1]$,
--
--   $$E_r\big(E_r^{-1}(y)\big)=y,$$
--
--   and for every $x\in[-1,1]$, $E_r^{-1}(E_r(x))=x$.
--
--   So the function the paper writes $E_r^{-1}$ — encoded as the inverse of $E_r$ on $[-1,1]$ — really is a two-sided inverse there. The paper uses this without comment when it Taylor-expands $E_r^{-1}$ and evaluates it at $t\,\beta(r,G)$, and again in Lemma 4.1 when it applies $E_r^{-1}(\beta\,f(u)\cdot f(v))$ to arbitrary inner products.
--
--   Two facts give it: $E_r$ maps $[-1,1]$ onto $[-1,1]$ (continuity with $E_r(0)=0$, $E_r(1)=1$, oddness) and $E_r$ is strictly increasing, hence injective, on $[-1,1]$. Surjectivity gives the right-inverse identity and injectivity the left-inverse one.
--
--   **Formalization Note** Downstream proofs can now use these two identities instead of unfolding `Function.invFunOn`, which is the reason the node exists.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Section 3, p. 88 (the inverse $E_r^{-1}$), and Proposition 4.2, p. 92.

import Mathlib
import Definitions.Def_Grothendieck_Series

open scoped BigOperators Real

namespace Grothendieck

/-- **`ErInv` is the inverse of `E_r` on `[-1,1]`** — both compositions. -/
theorem ErInv_isInverse (r : ℕ) (hr : 1 ≤ r) :
    (∀ y ∈ Set.Icc (-1 : ℝ) 1, Er r (ErInv r y) = y) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, ErInv r (Er r x) = x) := by sorry

end Grothendieck
