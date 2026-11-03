-- Prove2me | Theorems.Thm_FreeOrderEPTAS_constraints_I_III
-- name    : FreeOrderEPTAS.constraints_I_III
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:26:36.789307+00:00
-- url     : https://prove2.me/theorems/0af07121-d8b8-4bce-ab7c-6b65dffa772a
-- title:
--   §2.6 — X satisfies (I)–(III) with probability 1 (corrected: capped small-load guess)
-- statement:
--   Let $x^{(\mathrm{IP})}$ satisfy (II) and (III), and let the guesses be those it induces. For every vector $y$ meeting (S1)–(S3), every $Y$ in the support of a rounding with (P2) satisfies (II) and (III); (I) holds by type.
--
--   The chain for (III) is $\sum_jX_{ij}\le\sum_tN^\uparrow_{it}\le\sum_tN^{(\mathrm{IP})}_{it}=\sum_jx^{(\mathrm{IP})}_{ij}\le k_i$.
--
--   Differences from the source:
--   - correction: $S^\downarrow_{idt}=\lfloor S^{(\mathrm{IP})}_{idt}\rfloor_{\epsilon/T}$, p.10 → $S^\downarrow_{idt}=\lfloor\min\{S^{(\mathrm{IP})}_{idt},1\}\rfloor_{\epsilon/T}$; reason: the printed guess has order $n$ values ($n$ jobs of load $\delta$ in one class, all on machine $i$), a PTAS count against the stated $O((T/\epsilon)^{O(mDT)})$; every step of the proof survives the cap
--   - generalization: $y^*$, a feasible solution of (LP), for $x^{(\mathrm{IP})}$ feasible and $\xi=\epsilon/2$ → any $y$ meeting (S1)–(S3), any $x^{(\mathrm{IP})}$ satisfying (II), (III), any $\xi$; reason: the argument uses (P2), $N^\uparrow\le N^{(\mathrm{IP})}$ and (III) of $x^{(\mathrm{IP})}$ only; the source’s case is covered
--   - encoding: $X_{ij}=Y_{(i,\rho(j)),j}$ → the same binary matrix, $Y$ indexed by $(i,j)$; reason: $j$ meets one pair-vertex per machine
--   - encoding: "with probability 1" → for every point of the support of the law; reason: the laws are on a finite set
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §2.6, pp.12–13, displays (1)–(3)

import Mathlib
import Definitions.Def_FreeOrderEPTAS_mkLP
import Definitions.Def_FreeOrderEPTAS_IsInducedGuess
import Definitions.Def_FreeOrderEPTAS_IsDependentRounding

namespace FreeOrderEPTAS

/-- §2.6, pp.12–13 (arXiv:2007.13121v3): with probability 1, the rounded vector satisfies
constraints (I)–(III) of (IP): every `Y` in the support of the rounding of any `y` meeting
(S1)–(S3) is cardinality-feasible. -/
theorem constraints_I_III {m D n : ℕ} (I : SCInstance m D n) (ϵ δ ξ : ℝ)
    (x : Assignment m n) (hcard : MeetsCard I x)
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ)
    (hg : IsInducedGuess I ϵ δ ξ x Nlo Nhi Slo)
    (y : (mkLP I ϵ δ ξ Nlo Nhi Slo).Vars) (hy : (mkLP I ϵ δ ξ Nlo Nhi Slo).MeetsS123 y)
    (rnd : Rounding) (hrnd : IsDependentRounding rnd)
    (Y : Assignment m n) (hY : Y ∈ (rnd (mkLP I ϵ δ ξ Nlo Nhi Slo) y).support) :
    MeetsCard I Y := by sorry

end FreeOrderEPTAS
