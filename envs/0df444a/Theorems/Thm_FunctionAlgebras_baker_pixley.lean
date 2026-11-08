-- Prove2me | Theorems.Thm_FunctionAlgebras_baker_pixley
-- name    : FunctionAlgebras.baker_pixley
-- status  : Open
-- author  : @Alien60
-- created : 2026-11-07T16:59:33.270711+00:00
-- url     : https://prove2.me/theorems/191f3add-e850-4b59-8f11-1bb849acbd45
-- title:
--   Baker-Pixley theorem: C = Pol Inv_d C
-- statement:
--   $A$ is a set; operations are maps $A^n\to A$ ($n\ge0$). $C=(C_n)_n$ is a clone: it contains all projections and is closed under composition $f(g_0,\dots,g_{n-1})$. $C$ contains a $(d+1)$-ary near-unanimity operation $m$, i.e. $m(x,\dots,x,y,x,\dots,x)=x$ for every position of $y$, where $d\ge2$. An $n$-ary $f$ preserves $R\subseteq A^\iota$ if applying $f$ coordinatewise to any $n$ tuples of $R$ gives a tuple of $R$; $\mathrm{Inv}_k C$ is the set of $k$-ary relations preserved by all members of $C$. If $A$ is finite, then for every $n$ and every $n$-ary operation $f$: $f\in C_n$ if and only if $f$ preserves every relation in $\mathrm{Inv}_d C$. That is, $C=\mathrm{Pol}\,\mathrm{Inv}_d C$.
-- source:
--   D. Lau, Function Algebras on Finite Sets, Springer Monographs in Mathematics, 2006, https://doi.org/10.1007/3-540-36023-9, Part II, Theorem 8.3.1; K. A. Baker, A. F. Pixley, Polynomial interpolation and the Chinese remainder theorem for algebraic systems, Math. Z. 143 (1975) 165-174, https://doi.org/10.1007/BF01187059, Corollary 5.1

import Definitions.Def_FunctionAlgebras_defs

universe u

namespace FunctionAlgebras

variable {A : Type u}

/-- Lau, *Function Algebras on Finite Sets*, Part II, Theorem 8.3.1 (Baker–Pixley theorem;
Baker–Pixley 1975, Corollary 5.1).  Let `C` be a clone on a finite set containing a `(d+1)`-ary
near-unanimity operation, `d ≥ 2`.  Then `C = Pol Inv_d C`: an operation belongs to `C` if and
only if it preserves every `d`-ary invariant relation of `C`. -/
theorem baker_pixley [Finite A] (C : ∀ n : ℕ, Set ((Fin n → A) → A)) (hC : IsClone C) {d : ℕ}
    (hd : 2 ≤ d) (m : (Fin (d + 1) → A) → A) (hm : m ∈ C (d + 1)) (hnu : IsNearUnanimity m)
    (n : ℕ) (f : (Fin n → A) → A) :
    f ∈ C n ↔ ∀ R ∈ Inv C d, Preserves f R := by sorry

end FunctionAlgebras
