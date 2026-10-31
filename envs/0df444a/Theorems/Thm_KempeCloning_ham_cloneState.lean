-- Prove2me | Theorems.Thm_KempeCloning_ham_cloneState
-- name    : KempeCloning.ham_cloneState
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:24:57.297979+00:00
-- url     : https://prove2.me/theorems/bd2c995a-d966-483b-89cb-ab541c9d5a22
-- title:
--   Eq. (21): $\mathcal H$ acts tridiagonally on the $|\mathcal F_l\rangle$
-- statement:
--   Let $\gamma\in\mathbb R$, $m, N\in\mathbb N$, let $\mathcal H$ be the Hamiltonian (14) and $|\mathcal F_l\rangle$ the states (19). Then:
--
--   1. for $1\le l < N$,
--   $$\mathcal H|\mathcal F_l\rangle = \gamma\Big(\sqrt{(l+1)(N-l)(m+l+2)}\;|\mathcal F_{l+1}\rangle + \sqrt{l(N-l+1)(m+l+1)}\;|\mathcal F_{l-1}\rangle\Big);$$
--   2. if $N\ge1$, $\mathcal H|\mathcal F_0\rangle = \gamma\sqrt{N(m+2)}\;|\mathcal F_1\rangle$;
--   3. if $N\ge1$, $\mathcal H|\mathcal F_N\rangle = \gamma\sqrt{N(m+N+1)}\;|\mathcal F_{N-1}\rangle$;
--   4. if $N = 0$, $\mathcal H|\mathcal F_0\rangle = 0$.
--
--   In particular $\mathcal H$ maps the span of $|\mathcal F_0\rangle,\dots,|\mathcal F_N\rangle$ into itself, which is the step that completes the paper's proof of (18).
--
--   Differences from the source:
--   - reading: the lines for $\mathcal H|\mathcal F_0\rangle$ and $\mathcal H|\mathcal F_N\rangle$ stated without a condition on $N$ → hypothesis $1\le N$ on clauses 2 and 3; reason: at $N = 0$ these lines refer to $|\mathcal F_1\rangle$ and $|\mathcal F_{-1}\rangle$, which are not defined ($l$ ranges over $0,\dots,N$)
--   - generalization: no line for $N = 0$ → clause 4: $\mathcal H|\mathcal F_0\rangle = 0$ when $N = 0$; reason: an added case; the three printed lines are clauses 1–3 unchanged
--   - reading: "for arbitrary $N$ and $m$" (p.5) → every $m, N\in\mathbb N$, including $m = 0$ and $N = 0$; reason: the page does not exclude these values; the stronger reading is taken, and it specializes to $m, N\ge1$
--   - reading: coupling constant $\gamma$, whose type the page does not state → $\gamma\in\mathbb R$; reason: (21) is printed with the same $\gamma$ on the term from (14) and on its h.c., which holds only for real $\gamma$, and the page absorbs phases into $\gamma$ (p.4)
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II C, (21), p.5

import Definitions.Def_KempeCloning_ham
import Definitions.Def_KempeCloning_cloneState

namespace KempeCloning

/-- **The three-term recursion (21): `H` acts tridiagonally on the `|F_l⟩`.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II C, (21), p.5: "Explicit calculation shows
that
H|F_l⟩ = γ(√((l + 1)(N − l)(m + l + 2)) |F_{l+1}⟩ + √(l(N − l + 1)(m + l + 1)) |F_{l−1}⟩)   1 ≤ l < N
H|F_0⟩ = γ √(N(m + 2)) |F_1⟩
H|F_N⟩ = γ √(N(m + N + 1)) |F_{N−1}⟩ (21)
which completes the proof."

For every real `γ` and all `m, N`:
1. for `1 ≤ l < N`, `H|F_l⟩ = γ(√((l+1)(N−l)(m+l+2)) |F_{l+1}⟩ + √(l(N−l+1)(m+l+1)) |F_{l−1}⟩)`;
2. for `N ≥ 1`, `H|F_0⟩ = γ√(N(m+2)) |F_1⟩`;
3. for `N ≥ 1`, `H|F_N⟩ = γ√(N(m+N+1)) |F_{N−1}⟩`;
4. for `N = 0`, `H|F_0⟩ = 0`.

**Formalization Note.** The factors under the square roots are computed in `ℝ` (`N − l` as a real
difference, positive for `l < N`); the indices `l − 1` and `N − 1` are natural-number subtractions,
exact under the stated hypotheses `1 ≤ l` and `1 ≤ N`. Clause 4 covers the case `N = 0`, where the
paper's two end lines would refer to the nonexistent `|F_1⟩` and `|F_{−1}⟩`. -/
theorem ham_cloneState (γ : ℝ) (m N : ℕ) :
    (∀ l : ℕ, 1 ≤ l → l < N →
      ham γ (cloneState m N l) =
        (γ : ℂ) •
          ((((Real.sqrt (((l : ℝ) + 1) * ((N : ℝ) - l) * ((m : ℝ) + l + 2)) : ℝ) : ℂ) •
              cloneState m N (l + 1)) +
            (((Real.sqrt ((l : ℝ) * ((N : ℝ) - l + 1) * ((m : ℝ) + l + 1)) : ℝ) : ℂ) •
              cloneState m N (l - 1)))) ∧
    (1 ≤ N →
      ham γ (cloneState m N 0) =
        (γ : ℂ) • (((Real.sqrt ((N : ℝ) * ((m : ℝ) + 2)) : ℝ) : ℂ) • cloneState m N 1)) ∧
    (1 ≤ N →
      ham γ (cloneState m N N) =
        (γ : ℂ) •
          (((Real.sqrt ((N : ℝ) * ((m : ℝ) + N + 1)) : ℝ) : ℂ) • cloneState m N (N - 1))) ∧
    (N = 0 → ham γ (cloneState m N 0) = 0) := by sorry

end KempeCloning
