-- Prove2me | Theorems.Thm_FunctionAlgebras_local_interpolation
-- name    : FunctionAlgebras.local_interpolation
-- status  : Open
-- author  : @Alien60
-- created : 2026-11-07T16:59:12.004184+00:00
-- url     : https://prove2.me/theorems/5ec8b1c2-7206-420c-befe-8de2bfa02b1c
-- title:
--   Local-to-global interpolation
-- statement:
--   $A$ is a set; operations are maps $A^n\to A$ ($n\ge0$). $C=(C_n)_n$ is a clone: it contains all projections and is closed under composition $f(g_0,\dots,g_{n-1})$. $C$ contains a $(d+1)$-ary near-unanimity operation $m$, i.e. $m(x,\dots,x,y,x,\dots,x)=x$ for every position of $y$, where $d\ge2$. Let $n\ge1$, $f$ an $n$-ary partial function and $D\subseteq A^n$ a finite set (its domain). If for every $E\subseteq D$ with $|E|\le d$ some $p\in C_n$ agrees with $f$ on $E$, then some $p\in C_n$ agrees with $f$ on all of $D$.
-- source:
--   K. A. Baker, A. F. Pixley, Polynomial interpolation and the Chinese remainder theorem for algebraic systems, Math. Z. 143 (1975) 165-174, https://doi.org/10.1007/BF01187059, Theorem 2.1, (1) implies (4); D. Lau, Function Algebras on Finite Sets, Springer Monographs in Mathematics, 2006, https://doi.org/10.1007/3-540-36023-9, Part II, proof of Theorem 8.3.1, step II

import Definitions.Def_FunctionAlgebras_defs

universe u

namespace FunctionAlgebras

variable {A : Type u}

/-- Baker–Pixley (1975), Theorem 2.1, (1) ⇒ (4), for the clone `C` of term operations of an
algebra on `A` (Lau, proof of Theorem 8.3.1, step II).  If `C` contains a `(d+1)`-ary
near-unanimity operation (`d ≥ 2`), then a finite partial `n`-ary function `f` with domain `D`
is interpolated on `D` by a member of `C` as soon as its restriction to every subset of `D` with
at most `d` elements is. -/
theorem local_interpolation (C : ∀ n : ℕ, Set ((Fin n → A) → A)) (hC : IsClone C) {d : ℕ}
    (hd : 2 ≤ d) (m : (Fin (d + 1) → A) → A) (hm : m ∈ C (d + 1)) (hnu : IsNearUnanimity m)
    {n : ℕ} (hn : 0 < n) (f : (Fin n → A) → A) (D : Finset (Fin n → A))
    (hloc : ∀ E ⊆ D, E.card ≤ d → Interpolates C f ↑E) :
    Interpolates C f ↑D := by sorry

end FunctionAlgebras
