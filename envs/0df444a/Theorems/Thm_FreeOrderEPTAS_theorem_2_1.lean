-- Prove2me | Theorems.Thm_FreeOrderEPTAS_theorem_2_1
-- name    : FreeOrderEPTAS.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:35.480519+00:00
-- url     : https://prove2.me/theorems/d14d0d80-ba85-45c0-a031-b6b629f01212
-- title:
--   Theorem 2.1 — the Santa Claus EPTAS (corrected: capped small-load guess)
-- statement:
--   There are $f$ and a universal $d$ such that, for every $\varepsilon\in(0,1)$, every instance with $m$ machines, $D$ dimensions and $n$ jobs, every LP solver and every rounding with (P1)–(P3), the program `santaClaus` satisfies:
--
--   1. if (IP) is feasible then, with probability at least $1/2$, it returns an $X$ satisfying (I)–(III) with $\sum_{j}\ell_{ijd}X_{ij}\ge1-\varepsilon$ for all $i$ and $d\in A_i$;
--   2. every returned $X$ has these properties;
--   3. on every outcome, the counted cost is at most $f(\lceil1/\varepsilon\rceil,m,D)(n+1)^d$, and every LP and rounding instance has size at most $f(\lceil1/\varepsilon\rceil,m,D)(n+1)$.
--
--   This is the engine of the mission: the exponent of $n$ does not depend on $\varepsilon$, $m$ or $D$.
--
--   Differences from the source:
--   - correction: $S^\downarrow_{idt}=\lfloor S^{(\mathrm{IP})}_{idt}\rfloor_{\epsilon/T}$, p.10 → $S^\downarrow_{idt}=\lfloor\min\{S^{(\mathrm{IP})}_{idt},1\}\rfloor_{\epsilon/T}$; reason: the printed guess has order $n$ values ($n$ jobs of load $\delta$ in one class, all on machine $i$), a PTAS count against the stated $O((T/\epsilon)^{O(mDT)})$; every step of the proof survives the cap
--   - reading: "$t(\epsilon)\cdot\mathrm{poly}(n)$-time algorithm", with an oracle returning a real number and an LP solved inside → unit-cost real arithmetic, comparisons, floors, ceilings and logs; one counted call per oracle query, LP solve and rounding; instance sizes bounded by $t(\epsilon)(n+1)$; reason: the two primitives of the proof cannot both live in the bit model; with any polynomial LP solver and the polynomial GKPS procedure this gives $t(\epsilon)\cdot\mathrm{poly}(n)$
--   - reading: "guess" the parameters, pp.10, 18 → enumerate every guess vector, verify, keep what passes; reason: a deterministic reading of guessing
--   - reading: "guess an integer value $N^\uparrow_{it}\in[(1-\xi)N,N]$" with $O((1/\xi)\log n)$ options → the grid $g_k=\lceil(1-\xi)^{-k}\rceil$, $0\le k\le\lceil\log n/\log(1/(1-\xi))\rceil$; reason: the source leaves the grid unspecified; each integer $N\ge1$ has a $g_k$ in $[(1-\xi)N,N]$
--   - generalization: time $O(f(\epsilon,m,D)\cdot\mathrm{poly}(|I|))$ → cost $f(\lceil1/\varepsilon\rceil,m,D)(n+1)^d$; reason: $n\le|I|$; the numbers of the instance do not enter the count
--   - encoding: $\epsilon$, with Lemma 2.3 giving $2\epsilon$ → the program runs at $\epsilon=\varepsilon/2$; reason: the theorem’s $\epsilon$-violation is Lemma 2.3 at $\epsilon/2$
--   - encoding: $L_i\in\mathbb R^D_+$ and $\ell_{ij}\in\mathbb R^D_+$ → binary $L_i$, as $A_i$, and $\ell_{ijd}\in[0,1]$; reason: the assumptions the paper makes w.l.o.g. on p.8
--   - encoding: $\epsilon>0$ constant → $\varepsilon\in(0,1)$; reason: "small constants $\delta,\epsilon\in(0,1)$", p.9; for $\varepsilon\ge1$ the statement is about nothing the proof reaches
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Theorem 2.1, p.8 (= Theorem 1.5, p.6)

import Mathlib
import Definitions.Def_FreeOrderEPTAS_santaClaus

namespace FreeOrderEPTAS

/-- Theorem 2.1, p.8 (= Theorem 1.5, p.6) (arXiv:2007.13121v3), about the program `santaClaus`:
when (IP) is feasible, with probability at least 1/2 the output is an `X` satisfying (I)–(III) and
`∑_j ℓ_ijd X_ij ≥ 1 - ε`; every output is verified; and on every outcome the counted cost is at most
`f(⌈1/ε⌉, m, D) (n + 1)^d` and the LP and rounding instances have size at most
`f(⌈1/ε⌉, m, D) (n + 1)`, with `d` universal. -/
theorem theorem_2_1 :
    ∃ (f : ℕ → ℕ → ℕ → ℕ) (d : ℕ), ∀ (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (m D n : ℕ) (I : SCInstance m D n) (lp : LPSolver) (rnd : Rounding),
        IsLPSolver lp → IsDependentRounding rnd →
        (IPFeasible I → (1 / 2 : ℝ) ≤ pr ((santaClaus ε I lp rnd).run 0)
          {r | ∃ X, r.1 = some X ∧ MeetsCard I X ∧ LoadAtLeast I X (1 - ε)}) ∧
        ∀ r ∈ ((santaClaus ε I lp rnd).run 0).support,
          (∀ X, r.1 = some X → MeetsCard I X ∧ LoadAtLeast I X (1 - ε)) ∧
          r.2.total ≤ f ⌈1 / ε⌉₊ m D * (n + 1) ^ d ∧
          r.2.maxSize ≤ f ⌈1 / ε⌉₊ m D * (n + 1) := by sorry

end FreeOrderEPTAS
