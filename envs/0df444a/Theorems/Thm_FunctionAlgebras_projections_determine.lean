-- Prove2me | Theorems.Thm_FunctionAlgebras_projections_determine
-- name    : FunctionAlgebras.projections_determine
-- status  : Open
-- author  : @Alien60
-- created : 2026-11-07T16:59:22.168787+00:00
-- url     : https://prove2.me/theorems/068e96a8-5042-40cb-8db8-f05909b734c3
-- title:
--   Subpowers are determined by their d-fold projections
-- statement:
--   $A$ is a set; operations are maps $A^n\to A$ ($n\ge0$). $C=(C_n)_n$ is a clone: it contains all projections and is closed under composition $f(g_0,\dots,g_{n-1})$. $C$ contains a $(d+1)$-ary near-unanimity operation $m$, i.e. $m(x,\dots,x,y,x,\dots,x)=x$ for every position of $y$, where $d\ge2$. An $n$-ary $f$ preserves $R\subseteq A^\iota$ if applying $f$ coordinatewise to any $n$ tuples of $R$ gives a tuple of $R$; $\mathrm{Inv}_k C$ is the set of $k$-ary relations preserved by all members of $C$. Let $\iota$ be a finite set and $R,S\subseteq A^\iota$ relations preserved by every member of $C$. If for every $J\subseteq\iota$ with $|J|\le d$ the projections of $R$ and $S$ onto the coordinates $J$ coincide, then $R=S$.
-- source:
--   K. A. Baker, A. F. Pixley, Polynomial interpolation and the Chinese remainder theorem for algebraic systems, Math. Z. 143 (1975) 165-174, https://doi.org/10.1007/BF01187059, Theorem 2.1, (1) implies (2)

import Definitions.Def_FunctionAlgebras_defs

universe u

namespace FunctionAlgebras

variable {A : Type u}

/-- Baker–Pixley (1975), Theorem 2.1, (1) ⇒ (2), for the clone `C` of term operations of an
algebra on `A`.  If `C` contains a `(d+1)`-ary near-unanimity operation (`d ≥ 2`), then a
subuniverse `R` of a finite power `A^ι` is uniquely determined by its projections onto the sets
of at most `d` coordinates: two subuniverses with the same such projections are equal. -/
theorem projections_determine (C : ∀ n : ℕ, Set ((Fin n → A) → A)) (hC : IsClone C) {d : ℕ}
    (hd : 2 ≤ d) (m : (Fin (d + 1) → A) → A) (hm : m ∈ C (d + 1)) (hnu : IsNearUnanimity m)
    {ι : Type*} [Finite ι] (R S : Set (ι → A))
    (hR : ∀ (n : ℕ), ∀ f ∈ C n, Preserves f R) (hS : ∀ (n : ℕ), ∀ f ∈ C n, Preserves f S)
    (hproj : ∀ J : Finset ι, J.card ≤ d →
      (fun x : ι → A => fun j : J => x j) '' R = (fun x : ι → A => fun j : J => x j) '' S) :
    R = S := by sorry

end FunctionAlgebras
