-- Prove2me | Theorems.Thm_IsAlgClosed_algHom_symmetricPower_equiv_sym
-- name    : IsAlgClosed.algHom_symmetricPower_equiv_sym
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T06:52:29.173284+00:00
-- url     : https://prove2.me/theorems/a560e79a-d629-4cfb-843b-8c3c6e55c2f5
-- title:
--   Points of a symmetric power: $k$-algebra maps $(B^{\otimes g})^{S_g}\to k$ are unordered $g$-tuples of $k$-algebra maps $B\to k$
-- statement:
--   Let $k$ be an algebraically closed field, $B$ a commutative $k$-algebra and $g\ge0$. Let $B^{\otimes g}=B\otimes_k\cdots\otimes_k B$ ($g$ factors), on which the symmetric group $S_g$ acts by permuting the tensor factors,
--   $$\sigma\cdot(b_1\otimes\cdots\otimes b_g)=b_{\sigma^{-1}(1)}\otimes\cdots\otimes b_{\sigma^{-1}(g)},$$
--   and let $S=(B^{\otimes g})^{S_g}$ be the $k$-subalgebra of invariants. Geometrically, if $X=\operatorname{Spec}B$ then $B^{\otimes g}$ is the coordinate ring of $X^g$ and $S$ that of the symmetric power $\operatorname{Sym}^gX=X^g/S_g$. A $k$-algebra map $\psi:B^{\otimes g}\to k$ (a $k$-point of $X^g$) has coordinates $\psi_i=\psi\circ\iota_i:B\to k$, where $\iota_i(b)=1\otimes\cdots\otimes b\otimes\cdots\otimes1$ ($b$ in the $i$-th place), and $\psi\mapsto(\psi_1,\dots,\psi_g)$ is a bijection onto $g$-tuples of $k$-algebra maps $B\to k$.
--
--   Then there is a bijection
--   $$e:\operatorname{Hom}_{k\text{-alg}}(S,k)\;\xrightarrow{\ \sim\ }\;\operatorname{Sym}^g\big(\operatorname{Hom}_{k\text{-alg}}(B,k)\big)$$
--   onto the unordered $g$-tuples (multisets of size $g$) of $k$-algebra maps $B\to k$, such that for every $k$-algebra map $\psi:B^{\otimes g}\to k$ the restriction $\psi|_S$ goes to the multiset $\{\psi_1,\dots,\psi_g\}$ of its coordinates. Equivalently: every $k$-algebra map $S\to k$ extends to $B^{\otimes g}$, and two $k$-points of $X^g$ have the same restriction to $S$ exactly when their coordinate tuples differ by a permutation. So the $k$-points of $\operatorname{Sym}^gX$ are the unordered $g$-tuples of $k$-points of $X$; when $X$ is an affine curve these are the effective divisors of degree $g$ supported on $X$.
--
--   Role: this identifies the points of the charts $\operatorname{Sym}^g(\operatorname{Spec}B)$ of the symmetric power $\operatorname{Sym}^gC$ of a curve, from which the Jacobian is built (Weil, Chow, Milne). The extension step uses that $B^{\otimes g}$ is integral over $S$ (lying over) and that $k$ is algebraically closed; the fibre statement uses that $S_g$ acts transitively on the primes of $B^{\otimes g}$ over a given prime of $S$. For $B=k[x]$ it says that $k$-points of $\operatorname{Sym}^g\mathbb A^1$ are multisets of $g$ elements of $k$, i.e. monic polynomials of degree $g$ via their roots.
--
--   **Formalization Note**: $B^{\otimes g}$ is Mathlib's `PiTensorProduct k (fun _ : Fin g => B)` and the action of $\sigma\in S_g$ = `Equiv.Perm (Fin g)` is `PiTensorProduct.reindex k (fun _ : Fin g => B) σ`, which sends `tprod k b` to `tprod k (fun i => b (σ.symm i))`. The invariant subalgebra is the variable `S : Subalgebra k (PiTensorProduct k (fun _ : Fin g => B))`, fixed uniquely by its membership condition `hS` (an element lies in `S` iff it is fixed by every `σ`). The inclusion $\iota_i$ of the $i$-th factor is `PiTensorProduct.singleAlgHom i`, the restriction $\psi|_S$ is `ψ.comp S.val`, and an unordered $g$-tuple is an element of Mathlib's `Sym (B →ₐ[k] k) g` (a multiset of cardinality $g$), compared through its coercion to `Multiset`; `Finset.univ.val.map (fun i => ...)` is the multiset $\{\psi_1,\dots,\psi_g\}$. The compatibility is required for every $\psi$, so it is never vacuous; together with bijectivity of `e` it contains both the extension property and the description of the fibres. Example: $B=k[x]$ (`Polynomial k`), any $g$, and $S$ the invariant subalgebra.
-- source:
--   J. S. Milne, Jacobian Varieties, in: G. Cornell, J. H. Silverman (eds.), Arithmetic Geometry, Springer (1986), §3 (symmetric powers of a curve); D. Mumford, Abelian Varieties, Oxford University Press (1970), §3; N. Bourbaki, Commutative Algebra, Ch. V §2 (lying over and transitivity of the Galois action on fibres)

import Mathlib

set_option autoImplicit false

theorem IsAlgClosed.algHom_symmetricPower_equiv_sym
    {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B] (g : ℕ)
    (S : Subalgebra k (PiTensorProduct k (fun _ : Fin g => B)))
    (hS : ∀ x, x ∈ S ↔ ∀ σ : Equiv.Perm (Fin g), PiTensorProduct.reindex k (fun _ : Fin g => B) σ x = x) :
    ∃ e : (S →ₐ[k] k) ≃ Sym (B →ₐ[k] k) g,
      ∀ ψ : PiTensorProduct k (fun _ : Fin g => B) →ₐ[k] k,
        (e (ψ.comp S.val) : Multiset (B →ₐ[k] k)) =
          Finset.univ.val.map (fun i : Fin g => ψ.comp (PiTensorProduct.singleAlgHom i)) := by
  sorry
