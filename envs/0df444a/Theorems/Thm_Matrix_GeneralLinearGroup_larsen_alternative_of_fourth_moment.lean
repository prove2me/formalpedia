-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_larsen_alternative_of_fourth_moment
-- name    : Matrix.GeneralLinearGroup.larsen_alternative_of_fourth_moment
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T03:25:19.317478+00:00
-- url     : https://prove2.me/theorems/4ed7c364-1c12-4638-bc71-d57b16ede0cf
-- title:
--   Larsen's alternative: an irreducible Zariski closed subgroup of GL_n over an alg. closed field of characteristic 0 with fourth moment 2 (resp. 3) is finite or contains SL_n (resp. is SO, O, Sp)
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$, $V = K^n$, and let $G \le \mathrm{GL}_n(K)$ be a Zariski closed subgroup acting irreducibly on $V$. Its **fourth moment** is
--
--   $$M_4(G) = \dim_K \mathrm{End}_G(\mathrm{End}\,V) = \dim_K \{\varphi : M_n(K) \to M_n(K) \text{ linear} : \varphi(g x g^{-1}) = g\,\varphi(x)\,g^{-1} \ \forall g \in G\},$$
--
--   which equals $\dim (V \otimes V \otimes V^\vee \otimes V^\vee)^G$ (over $\mathbb C$, for compact $G$ this is $\int_G |\mathrm{tr}\, g|^4\, dg$). Then (**Larsen's alternative**):
--
--   1. if $n \ge 2$, $\det(G)$ is finite and $M_4(G) = 2$, then $G$ is finite, or $\mathrm{SL}_n(K) \le G$ (with finite index);
--   2. if $n \ge 3$, $B$ is a nondegenerate symmetric bilinear form, $G \le \mathrm{O}(B)$ and $M_4(G) = 3$, then $G$ is finite, or $G = \mathrm{SO}(B)$, or $G = \mathrm{O}(B)$;
--   3. if $n \ge 3$, $B$ is a nondegenerate alternating bilinear form, $G \le \mathrm{Sp}(B)$ and $M_4(G) = 3$, then $G$ is finite or $G = \mathrm{Sp}(B)$.
--
--   Role: this is the standard tool (Larsen; Katz) for computing geometric monodromy groups of $\ell$-adic sheaves from moment computations: the fourth moment of traces of Frobenius is computed by point counting, and Larsen's alternative then identifies the monodromy group, as in Katz's work on Kloosterman sums and Lefschetz pencils.
--
--   **Formalization Note**: $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` (rows and columns indexed by a finite type `n`, $n = $ `Fintype.card n`). Zariski closed is written out: there is a set $S$ of polynomials in $2n^2$ variables (`MvPolynomial ((n × n) ⊕ (n × n)) K`) such that $g \in G$ iff every $p \in S$ vanishes at the entries of $g$ and $g^{-1}$ (the coordinate ring of $\mathrm{GL}_n$). Irreducibility: every $G$-stable subspace `W` of `n → K` is `⊥` or `⊤`. $M_4(G)$ is `M`, the `Module.finrank` of the span of the set of linear maps $\varphi$ above (that set is already a subspace, so the span is the set itself). $\det(G)$ finite is the finiteness of the image of `det` on `G`; $\mathrm{SL}_n(K)$ is the kernel of `Matrix.GeneralLinearGroup.det`, and "finite index" is `Subgroup.FiniteIndex` of `SL_n ∩ G` in `G` (`subgroupOf`). $\mathrm{O}(B) = \{g : g^T B g = B\}$, $\mathrm{SO}(B) = \mathrm{O}(B) \cap \{\det g = 1\}$, $\mathrm{Sp}(B) = \{g : g^T B g = B\}$ for alternating $B$, written as membership equivalences; symmetric is `Matrix.transpose B = B`, alternating (char 0) is `Matrix.transpose B = -B`, and nondegenerate is `Matrix.Nondegenerate`. Finite `G` is `Finite G`.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; M. Larsen, The normal distribution as a limit of generalized Sato-Tate measures, preprint (c. 1993); A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.larsen_alternative_of_fourth_moment
    {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (G : Subgroup (Matrix.GeneralLinearGroup n K))
    (hGc : ∃ S : Set (MvPolynomial ((n × n) ⊕ (n × n)) K), ∀ g : Matrix.GeneralLinearGroup n K,
      g ∈ G ↔ ∀ p ∈ S, MvPolynomial.eval (Sum.elim (fun ij : n × n => (g : Matrix n n K) ij.1 ij.2)
        (fun ij : n × n => ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ij.1 ij.2)) p = 0)
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, Matrix.mulVec (g : Matrix n n K) v ∈ W) → W = ⊥ ∨ W = ⊤)
    (M : ℕ)
    (hM : Module.finrank K (Submodule.span K {φ : Matrix n n K →ₗ[K] Matrix n n K | ∀ g ∈ G,
      ∀ x : Matrix n n K, φ ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
        (g : Matrix n n K) * φ x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)}) = M) :
    (2 ≤ Fintype.card n →
        ((fun g : Matrix.GeneralLinearGroup n K => (g : Matrix n n K).det) ''
          (G : Set (Matrix.GeneralLinearGroup n K))).Finite → M = 2 →
        Finite G ∨ ((Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup n K →* Kˣ).ker ≤ G ∧
          ((Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup n K →* Kˣ).ker.subgroupOf G).FiniteIndex)) ∧
      (3 ≤ Fintype.card n → ∀ B : Matrix n n K, Matrix.transpose B = B → B.Nondegenerate →
        (∀ g ∈ G, Matrix.transpose (g : Matrix n n K) * B * g = B) → M = 3 →
        Finite G ∨
          (∀ g : Matrix.GeneralLinearGroup n K,
            g ∈ G ↔ (Matrix.transpose (g : Matrix n n K) * B * g = B ∧ (g : Matrix n n K).det = 1)) ∨
          (∀ g : Matrix.GeneralLinearGroup n K, g ∈ G ↔ Matrix.transpose (g : Matrix n n K) * B * g = B)) ∧
      (3 ≤ Fintype.card n → ∀ B : Matrix n n K, Matrix.transpose B = -B → B.Nondegenerate →
        (∀ g ∈ G, Matrix.transpose (g : Matrix n n K) * B * g = B) → M = 3 →
        Finite G ∨ (∀ g : Matrix.GeneralLinearGroup n K, g ∈ G ↔ Matrix.transpose (g : Matrix n n K) * B * g = B)) := by sorry
