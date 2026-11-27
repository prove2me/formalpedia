-- Prove2me | Theorems.Thm_NadlerCLS_holderSearch_check_P
-- name    : NadlerCLS.holderSearch_check_P
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-26T23:29:01.701812+00:00
-- url     : https://prove2.me/theorems/033c3950-66b4-588f-ab99-b69a7a356f3d
-- title:
--   Answers of $\beta$-Hölder-LocalOpt are verifiable in polynomial time
-- statement:
--   Answers of $\beta$-Hölder-LocalOpt can be verified in polynomial time.
--
--   Fix a dimension $n$, a rational exponent $\beta\in(0,1]$ and a natural number $k$. Consider $\beta$-Hölder-LocalOpt on $[0,1]^n$ (instances: well-behaved circuits $f:[0,1]^n\to[0,1]^n$, $p:[0,1]^n\to[0,1]$ and rationals $\delta,\lambda>0$; answers (HO1)–(HO3) of Definition 5) with answers restricted to strings $t$ of length
--
--   $$|t|\le(|s|+1)^k+k,$$
--
--   where $s$ is the binary code of the instance. Then the checking language
--
--   $$L=\{\,s\#t\;:\;s\text{ is the code of a valid instance and }t\text{ is an answer of length at most }(|s|+1)^k+k\,\}$$
--
--   is in $\mathrm P$.
--
--   This is the verification condition of TFNP for $\beta$-Hölder-LocalOpt, used for its CLS-membership (Theorem C.4).
--
--   **Formalization Note** The problem is the public `bounded (holderSearch n β) k`, its checking language is Cook's `checkLang` over `Option (Bool ⊕ Bool)`, and $\mathrm P$ is `CookPvsNP.P`.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101v4, Definition 5, p.31, and Theorem C.4, p.37 (CLS-completeness of β-HÖLDER-LOCALOPT, which includes membership in TFNP); circuits evaluate their rational outputs exactly (Section 3, p.9).

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NadlerCLS_holderSearch

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

theorem holderSearch_check_P (n : ℕ) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (k : ℕ) :
    CookPvsNP.checkLang (fun x y => (bounded (holderSearch n β) k).valid x ∧
      (bounded (holderSearch n β) k).answer x y) ∈ CookPvsNP.P (Option (Bool ⊕ Bool)) := by sorry

end NadlerCLS
