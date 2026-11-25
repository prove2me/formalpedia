-- Prove2me | Theorems.Thm_Matrix_isOpen_setOf_le_rank_map_residueField
-- name    : Matrix.isOpen_setOf_le_rank_map_residueField
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:08:04.989861+00:00
-- url     : https://prove2.me/theorems/c18cb2fe-186a-4838-baf8-6abce7d1e02f
-- title:
--   Lower semicontinuity of the rank of a matrix over Spec A: the primes where the reduction has rank at least s form an open set
-- statement:
--   Let $A$ be a commutative ring, let $m$ and $n$ be finite index sets, let $M = (a_{ij}) \in A^{m \times n}$ be a matrix with entries in $A$, and let $s \in \mathbb{N}$. For a prime ideal $\mathfrak{p} \in \operatorname{Spec} A$ let $\kappa(\mathfrak{p}) = \operatorname{Frac}(A/\mathfrak{p})$ be its residue field and let $M(\mathfrak{p}) \in \kappa(\mathfrak{p})^{m \times n}$ be the reduction of $M$ at $\mathfrak{p}$ (apply $A \to \kappa(\mathfrak{p})$ to every entry). Then the set
--
--   $$\{\mathfrak{p} \in \operatorname{Spec} A : \operatorname{rank}_{\kappa(\mathfrak{p})} M(\mathfrak{p}) \ge s\}$$
--
--   is open in the Zariski topology on $\operatorname{Spec} A$. In other words, the fibrewise rank $\mathfrak{p} \mapsto \operatorname{rank} M(\mathfrak{p})$ is lower semicontinuous on $\operatorname{Spec} A$, and correspondingly $\mathfrak{p} \mapsto \dim_{\kappa(\mathfrak{p})} \ker M(\mathfrak{p}) = |n| - \operatorname{rank} M(\mathfrak{p})$ is upper semicontinuous. The reason is that over a field the rank is at least $s$ exactly when some $s \times s$ minor is nonzero, and the $s \times s$ minors of $M(\mathfrak{p})$ are the images of those of $M$, so the set is the union of the basic open sets $D(\det M_{I,J})$ over all $s \times s$ minors $M_{I,J}$ of $M$ (the complement of the zero locus of the $s$-th determinantal ideal). This is the basic semicontinuity statement behind the openness of conditions such as $\ell(D) \le r$ or $\ell(D) = 1$ in families whose Riemann–Roch spaces are kernels of one matrix over the base.
--
--   **Formalization Note**: the residue field $\kappa(\mathfrak{p})$ is Mathlib's `p.asIdeal.ResidueField` (`Ideal.ResidueField`, the fraction field of `A ⧸ p.asIdeal`), and $M(\mathfrak{p})$ is `M.map (algebraMap A p.asIdeal.ResidueField)`. `Matrix.rank` is the dimension of the range of `M(p).mulVecLin`, the usual rank over a field. The index types `m`, `n` are arbitrary `Fintype`s. For $s = 0$ the set is all of $\operatorname{Spec} A$, and for $s > \min(|m|, |n|)$ it is empty; for $0 < s \le \min(|m|, |n|)$ it can be a proper nonempty open subset (e.g. $A = \mathbb{Z}$, $M = (\ell)$ for a prime number $\ell$, $s = 1$: the set is $\operatorname{Spec}\mathbb{Z} \setminus \{(\ell)\}$).
-- source:
--   Classical (determinantal / Fitting-ideal description of rank loci); see e.g. D. Eisenbud, Commutative Algebra with a View Toward Algebraic Geometry, GTM 150, Springer 1995, Chapter 20 (Fitting ideals)

import Mathlib

set_option autoImplicit false

theorem Matrix.isOpen_setOf_le_rank_map_residueField {A : Type*} [CommRing A] {m n : Type*}
    [Fintype m] [Fintype n] (M : Matrix m n A) (s : ℕ) :
    IsOpen {p : PrimeSpectrum A | s ≤ (M.map (algebraMap A p.asIdeal.ResidueField)).rank} := by
  sorry
