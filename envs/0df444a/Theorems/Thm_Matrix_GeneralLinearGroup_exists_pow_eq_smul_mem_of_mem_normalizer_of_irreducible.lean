-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_exists_pow_eq_smul_mem_of_mem_normalizer_of_irreducible
-- name    : Matrix.GeneralLinearGroup.exists_pow_eq_smul_mem_of_mem_normalizer_of_irreducible
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-14T06:02:45.807016+00:00
-- url     : https://prove2.me/theorems/e6599b74-f760-4afc-a4a6-52d9f525ec2e
-- title:
--   Elements normalising an irreducible finite, SL_n-containing, O(B), SO(B) or Sp(B) subgroup G of GL_n have a uniform power in K^× · G (Katz)
-- statement:
--   Let $K$ be an algebraically closed field (of any characteristic), $V = K^n$, and let $G \le \mathrm{GL}_n(K)$ be a subgroup acting irreducibly on $V$. Assume that one of the following holds:
--
--   - $G$ is finite;
--   - $\mathrm{SL}_n(K) \le G$;
--   - $G = \mathrm{O}(B) = \{g : g^{T} B g = B\}$ or $G = \mathrm{SO}(B) = \mathrm{O}(B) \cap \mathrm{SL}_n(K)$ for a nondegenerate bilinear form $B$ (for alternating $B$ this is $\mathrm{Sp}(B)$).
--
--   Then there is an integer $M > 0$, depending only on $G$, such that for every $\varphi \in \mathrm{GL}_n(K)$ normalising $G$:
--
--   1. $\varphi^M = c\,g$ for some scalar $c \in K$ and some $g \in G$;
--   2. for every representation $\rho : \mathrm{GL}_n(K) \to \mathrm{GL}(W)$ on a $K$-vector space $W$ that is trivial on the scalar matrices (for example $W = (V \otimes V^\vee)^{\otimes a} = \mathrm{End}(V)^{\otimes a}$), $\rho(\varphi)^M$ acts trivially on the $G$-coinvariants $W_G = W / \langle \rho(g)w - w : g \in G,\ w \in W \rangle$ and fixes every $G$-invariant vector, and every eigenvalue $\mu$ of $\rho(\varphi)$ on $W_G$ satisfies $\mu^M = 1$.
--
--   One can take $M = \#\mathrm{Sym}(G)$ if $G$ is finite (then $\varphi^M$ centralises $G$ and is scalar by Schur's lemma), $M = 1$ if $\mathrm{SL}_n(K) \le G$, and $M = 2$ in the orthogonal and symplectic cases (a normalising $\varphi$ is a similitude, $\varphi^{T} B \varphi = c B$).
--
--   Role: in Katz's account of Deligne's equidistribution argument, $\varphi$ is the image of an element of the arithmetic fundamental group, which normalises the geometric monodromy group $G = G_{\mathrm{geom}}$; the theorem shows that the eigenvalues of Frobenius on the $G_{\mathrm{geom}}$-coinvariants of $(V \otimes V^\vee)^{\otimes a}$ are roots of unity for every $a \ge 1$.
--
--   **Formalization Note**: $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` (rows and columns indexed by a finite type `n`). Irreducibility: every subspace `W` of `n → K` stable under all `Matrix.mulVec g`, $g \in G$, is `⊥` or `⊤`. Finite $G$ is `Finite G`; $\mathrm{SL}_n(K) \le G$ is: every `g` with `det g = 1` lies in `G`. The cases $G = \mathrm{O}(B)$, $G = \mathrm{SO}(B)$ are membership equivalences with `Matrix.transpose g * B * g = B` (and `det g = 1`), with `B.Nondegenerate`; no symmetry of $B$ is assumed, so the symplectic group of an alternating $B$ is included. The normaliser is `Subgroup.normalizer (G : Set _)`, and conclusion 1 is `((φ ^ M : GL) : Matrix n n K) = c • g`. A representation is a monoid hom `ρ : Matrix.GeneralLinearGroup n K →* Module.End K W` with `ρ s = 1` whenever `s = c • 1`; the coinvariants are the quotient by `C = Submodule.span K {ρ g u - u}`, so "acts trivially on $W_G$" is `ρ (φ ^ M) v - v ∈ C` for all `v`, and "$\mu$ is an eigenvalue of $\varphi$ on $W/C$" is: some `v ∉ C` has `ρ φ v - μ • v ∈ C`. The integer `M` is chosen before `W` and `ρ`, so it is uniform in the representation.
-- source:
--   N. M. Katz, L-functions and monodromy: four lectures on Weil II, Adv. Math. 160 (2001), 81-132 (Arizona Winter School 2000 notes), Lecture IV, the argument following the Positive Trace Corollary (pp. 22-23 of the notes)

import Mathlib

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.exists_pow_eq_smul_mem_of_mem_normalizer_of_irreducible
    {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K] [IsAlgClosed K]
    (G : Subgroup (Matrix.GeneralLinearGroup n K))
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, Matrix.mulVec (g : Matrix n n K) v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hcase : Finite G ∨
      (∀ g : Matrix.GeneralLinearGroup n K, (g : Matrix n n K).det = 1 → g ∈ G) ∨
      ∃ B : Matrix n n K, B.Nondegenerate ∧
        ((∀ g : Matrix.GeneralLinearGroup n K, g ∈ G ↔ Matrix.transpose (g : Matrix n n K) * B * g = B) ∨
          (∀ g : Matrix.GeneralLinearGroup n K,
            g ∈ G ↔ (Matrix.transpose (g : Matrix n n K) * B * g = B ∧ (g : Matrix n n K).det = 1)))) :
    ∃ M : ℕ, 0 < M ∧
      (∀ φ ∈ Subgroup.normalizer (G : Set (Matrix.GeneralLinearGroup n K)),
        ∃ c : K, ∃ g ∈ G, ((φ ^ M : Matrix.GeneralLinearGroup n K) : Matrix n n K) = c • (g : Matrix n n K)) ∧
      ∀ (W : Type*) [AddCommGroup W] [Module K W] (ρ : Matrix.GeneralLinearGroup n K →* Module.End K W),
        (∀ (s : Matrix.GeneralLinearGroup n K) (c : K), (s : Matrix n n K) = c • (1 : Matrix n n K) → ρ s = 1) →
        ∀ φ ∈ Subgroup.normalizer (G : Set (Matrix.GeneralLinearGroup n K)),
          (∀ v : W, ρ (φ ^ M) v - v ∈ Submodule.span K {w : W | ∃ g ∈ G, ∃ u : W, w = ρ g u - u}) ∧
          (∀ v : W, (∀ g ∈ G, ρ g v = v) → ρ (φ ^ M) v = v) ∧
          ∀ (μ : K) (v : W), v ∉ Submodule.span K {w : W | ∃ g ∈ G, ∃ u : W, w = ρ g u - u} →
            ρ φ v - μ • v ∈ Submodule.span K {w : W | ∃ g ∈ G, ∃ u : W, w = ρ g u - u} → μ ^ M = 1 := by
  sorry
