-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_lie_traceForm_nondegenerate_of_irreducible
-- name    : Matrix.GeneralLinearGroup.lie_traceForm_nondegenerate_of_irreducible
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T10:18:37.393391+00:00
-- url     : https://prove2.me/theorems/c3eeddc7-dccb-47e3-bb6a-bcf7d926f345
-- title:
--   Nondegenerate trace form on Lie algebras normalised by an irreducible subgroup of $\mathrm{GL}_n$, and the dichotomy $\mathrm{Lie} = 0$ or $\mathfrak{sl}_n$, $\mathfrak{o}(B)$
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and $n \ge 0$. View $\mathrm{GL}_n(K)$ as the affine variety $\{(A, A') \in M_n(K)^2 : A A' = 1\}$, with coordinates the entries of $g$ and of $g^{-1}$, so its coordinate functions are polynomials $f$ in $2n^2$ variables. The **Lie algebra** of a subset $Z \subseteq \mathrm{GL}_n(K)$ (for $1 \in Z$: the tangent space at $1$ of its Zariski closure) is
--
--   $$\mathrm{Lie}(Z) = \{X \in M_n(K) : D_{(X, -X)} f(1, 1) = 0 \text{ for every } f \text{ vanishing on } Z\},$$
--
--   where $D_{(X,-X)} f(1,1) = \sum_{i,j} \frac{\partial f}{\partial a_{ij}}(1,1) X_{ij} - \sum_{i,j} \frac{\partial f}{\partial a'_{ij}}(1,1) X_{ij}$ is the derivative at the identity in the direction of the curve $1 + \varepsilon X$ (whose inverse is $1 - \varepsilon X$ to first order). Let $G \le \mathrm{GL}_n(K)$ be a subgroup acting **irreducibly** on $K^n$ (the only $G$-stable subspaces are $0$ and $K^n$). Then:
--
--   1. if $H \le \mathrm{GL}_n(K)$ is a subgroup whose Lie algebra is stable under conjugation by $G$ ($g X g^{-1} \in \mathrm{Lie}(H)$ for $g \in G$, $X \in \mathrm{Lie}(H)$; for instance $G$ normalises $H$), then the trace form $(X, Y) \mapsto \mathrm{tr}(XY)$ is nondegenerate on $\mathrm{Lie}(H)$: if $X \in \mathrm{Lie}(H)$ and $\mathrm{tr}(XY) = 0$ for all $Y \in \mathrm{Lie}(H)$, then $X = 0$;
--   2. if every linear map $\varphi : M_n(K) \to M_n(K)$ that maps $\mathfrak{sl}_n = \{X : \mathrm{tr} X = 0\}$ into itself and commutes there with conjugation by every $g \in G$ is a scalar on $\mathfrak{sl}_n$ (that is, $\mathrm{End}_G(\mathfrak{sl}_n) = K$), then $\mathrm{Lie}(G \cap \mathrm{SL}_n(K))$ is $0$ or all of $\mathfrak{sl}_n$;
--   3. if $B \in M_n(K)$ and $G$ preserves the bilinear form of $B$ ($g^T B g = B$ for $g \in G$), and every linear map that maps $\mathfrak{o}(B) = \{X : X^T B + B X = 0\}$ into itself and commutes there with conjugation by $G$ is a scalar on $\mathfrak{o}(B)$, then $\mathrm{Lie}(G)$ is $0$ or all of $\mathfrak{o}(B)$ (for symmetric $B$ this is $\mathfrak{so}(B)$, for alternating $B$ it is $\mathfrak{sp}(B)$).
--
--   Role: part 1 replaces Weyl's complete reducibility theorem in the Lie-algebra step of Larsen's alternative: a Lie algebra $L \subseteq \mathfrak{sl}_n$ or $\mathfrak{o}(B)$ that is $\mathrm{Ad}(G)$-stable has, by nondegeneracy of the trace form, an $\mathrm{Ad}(G)$-stable complement, and the trace-form orthogonal projection onto $L$ is $G$-equivariant; when the ambient Lie algebra has only scalar $G$-endomorphisms, this projection is $0$ or the identity, which is parts 2 and 3. Combined with the Lie-algebra criteria ($\mathrm{Lie}(H) = 0 \Rightarrow H$ finite; $\mathrm{Lie}(H) \supseteq \mathfrak{sl}_n, \mathfrak{sp}(B), \mathfrak{so}(B) \Rightarrow H \supseteq \mathrm{SL}_n, \mathrm{Sp}(B), \mathrm{SO}(B)$), this shows that a Zariski closed irreducible $G$ with small fourth moment is finite or contains the corresponding classical group. Part 1 fails without the irreducibility hypothesis (take $G = H$ the upper unitriangular group: its Lie algebra consists of strictly upper triangular matrices, on which the trace form vanishes identically), and in characteristic $p$ (for $n = p$, the scalars $K^\times \subseteq \mathrm{GL}_p$, normalised by all of $\mathrm{GL}_p$, have Lie algebra $K \cdot 1$, and $\mathrm{tr}(1 \cdot 1) = p = 0$).
--
--   **Formalization Note**: $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with rows and columns indexed by a finite type `n`. The coordinate functions are `MvPolynomial ((n × n) ⊕ (n × n)) K`: the variable `Sum.inl (i, j)` is the entry $g_{ij}$ and `Sum.inr (i, j)` is the entry $(g^{-1})_{ij}$; `crd g` is the point of $K^{2n^2}$ given by these entries (pinned down by `hcrd`). `lie Z` is $\mathrm{Lie}(Z)$ (pinned down by `hlie`): `MvPolynomial.pderiv v f` is $\partial f / \partial x_v$, `crd 1` is the identity point, and `Sum.elim (fun ij => X ij.1 ij.2) (fun ij => -X ij.1 ij.2)` is the tangent vector $(X, -X)$. `crd` and `lie` are uniquely determined by `hcrd` and `hlie`, which only abbreviate these formulas. `hG` says that every subspace `W` of `n → K` with `Matrix.mulVec g v ∈ W` for all `g ∈ G`, `v ∈ W` is `⊥` or `⊤` (irreducibility). In part 1, `((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)` is the matrix $g^{-1}$ and `(X * Y).trace` is $\mathrm{tr}(XY)$. In part 2 the hypothesis on `φ` (a `K`-linear map `Matrix n n K →ₗ[K] Matrix n n K`) is $\mathrm{End}_G(\mathfrak{sl}_n) = K$, stated for maps of the whole matrix space through their restriction to `{X | X.trace = 0}` (every endomorphism of $\mathfrak{sl}_n$ extends to one), and `{g | g ∈ G ∧ (g : Matrix n n K).det = 1}` is $G \cap \mathrm{SL}_n(K)$. In part 3 `(g : Matrix n n K).transpose * B * g = B` says $g$ preserves $B$, and `{X | X.transpose * B + B * X = 0}` is $\mathfrak{o}(B)$; $B$ is arbitrary there (no symmetry or nondegeneracy is needed). `lie _ = {0}` is $\mathrm{Lie} = 0$. All types are in `Type`.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in Contributions to Automorphic Forms, Geometry, and Number Theory, Johns Hopkins Univ. Press 2004, 521-560 (Lie-algebra step); C. Chevalley, Theorie des groupes de Lie, Tome II, Hermann 1951 (replicas); J. E. Humphreys, Linear Algebraic Groups, Graduate Texts in Mathematics 21, Springer 1975, Sections 9 and 13; N. Bourbaki, Lie Groups and Lie Algebras, Chapter I, Section 6 (trace forms of faithful representations)

import Mathlib

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.lie_traceForm_nondegenerate_of_irreducible
    (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    (crd : Matrix.GeneralLinearGroup n K → (n × n) ⊕ (n × n) → K)
    (hcrd : ∀ g, crd g = Sum.elim (fun ij => (g : Matrix n n K) ij.1 ij.2)
      (fun ij => ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ij.1 ij.2))
    (lie : Set (Matrix.GeneralLinearGroup n K) → Set (Matrix n n K))
    (hlie : ∀ Z X, X ∈ lie Z ↔ ∀ f : MvPolynomial ((n × n) ⊕ (n × n)) K,
      (∀ g ∈ Z, MvPolynomial.eval (crd g) f = 0) →
        ∑ v, MvPolynomial.eval (crd 1) (MvPolynomial.pderiv v f) *
          Sum.elim (fun ij => X ij.1 ij.2) (fun ij => -X ij.1 ij.2) v = 0)
    (G : Subgroup (Matrix.GeneralLinearGroup n K))
    (hG : ∀ W : Submodule K (n → K),
      (∀ g ∈ G, ∀ v ∈ W, Matrix.mulVec (g : Matrix n n K) v ∈ W) → W = ⊥ ∨ W = ⊤) :
    (∀ H : Subgroup (Matrix.GeneralLinearGroup n K),
      (∀ g ∈ G, ∀ X ∈ lie H,
        (g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ∈ lie H) →
        ∀ X ∈ lie H, (∀ Y ∈ lie H, (X * Y).trace = 0) → X = 0) ∧
    ((∀ φ : Matrix n n K →ₗ[K] Matrix n n K,
        (∀ X : Matrix n n K, X.trace = 0 → (φ X).trace = 0) →
        (∀ g ∈ G, ∀ X : Matrix n n K, X.trace = 0 →
          φ ((g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
            (g : Matrix n n K) * φ X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) →
        ∃ c : K, ∀ X : Matrix n n K, X.trace = 0 → φ X = c • X) →
      lie {g | g ∈ G ∧ (g : Matrix n n K).det = 1} = {0} ∨
        lie {g | g ∈ G ∧ (g : Matrix n n K).det = 1} = {X | X.trace = 0}) ∧
    (∀ B : Matrix n n K, (∀ g ∈ G, (g : Matrix n n K).transpose * B * g = B) →
      (∀ φ : Matrix n n K →ₗ[K] Matrix n n K,
        (∀ X : Matrix n n K, X.transpose * B + B * X = 0 → (φ X).transpose * B + B * φ X = 0) →
        (∀ g ∈ G, ∀ X : Matrix n n K, X.transpose * B + B * X = 0 →
          φ ((g : Matrix n n K) * X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
            (g : Matrix n n K) * φ X * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) →
        ∃ c : K, ∀ X : Matrix n n K, X.transpose * B + B * X = 0 → φ X = c • X) →
      lie G = {0} ∨ lie G = {X | X.transpose * B + B * X = 0}) := by
  sorry
